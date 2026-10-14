import Mathlib.CategoryTheory.Category.Basic

/-!
# Categories modulo equality of coded arrows

A raw category whose laws hold modulo a compatible equivalence relation on
each hom type yields an ordinary category by quotienting the hom types.
-/

universe u v

namespace Kucera

class RawCategoryModulo (C : Type u) where
  Hom : C → C → Type v
  Rel : {X Y : C} → Hom X Y → Hom X Y → Prop
  rel_refl : ∀ {X Y} (f : Hom X Y), Rel f f
  rel_symm : ∀ {X Y} {f g : Hom X Y}, Rel f g → Rel g f
  rel_trans : ∀ {X Y} {f g h : Hom X Y}, Rel f g → Rel g h → Rel f h
  id : (X : C) → Hom X X
  comp : {X Y Z : C} → Hom X Y → Hom Y Z → Hom X Z
  comp_respects : ∀ {X Y Z} {f f' : Hom X Y} {g g' : Hom Y Z},
    Rel f f' → Rel g g' → Rel (comp f g) (comp f' g')
  id_comp_mod : ∀ {X Y} (f : Hom X Y), Rel (comp (id X) f) f
  comp_id_mod : ∀ {X Y} (f : Hom X Y), Rel (comp f (id Y)) f
  assoc_mod : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    Rel (comp (comp f g) h) (comp f (comp g h))

namespace RawCategoryModulo

variable {C : Type u} [R : RawCategoryModulo.{u,v} C]

instance homSetoid (X Y : C) : Setoid (R.Hom X Y) where
  r := R.Rel
  iseqv := ⟨R.rel_refl, R.rel_symm, R.rel_trans⟩

abbrev QHom (X Y : C) : Type v := Quotient (homSetoid (R := R) X Y)

def qid (X : C) : QHom (R := R) X X := Quotient.mk' (R.id X)

def qcomp {X Y Z : C} (f : QHom (R := R) X Y)
    (g : QHom (R := R) Y Z) : QHom (R := R) X Z :=
  Quotient.liftOn₂ f g (fun f g => Quotient.mk' (R.comp f g))
    (by
      intro f f' g g' hf hg
      exact Quotient.sound (R.comp_respects hf hg))

theorem qid_comp {X Y : C} (f : QHom (R := R) X Y) :
    qcomp (qid (R := R) X) f = f := by
  refine Quotient.inductionOn f ?_
  intro f
  exact Quotient.sound (R.id_comp_mod f)

theorem qcomp_id {X Y : C} (f : QHom (R := R) X Y) :
    qcomp f (qid (R := R) Y) = f := by
  refine Quotient.inductionOn f ?_
  intro f
  exact Quotient.sound (R.comp_id_mod f)

theorem qassoc {W X Y Z : C}
    (f : QHom (R := R) W X) (g : QHom (R := R) X Y)
    (h : QHom (R := R) Y Z) :
    qcomp (qcomp f g) h = qcomp f (qcomp g h) := by
  refine Quotient.inductionOn f ?_
  intro f
  refine Quotient.inductionOn g ?_
  intro g
  refine Quotient.inductionOn h ?_
  intro h
  exact Quotient.sound (R.assoc_mod f g h)

def quotientCategory : Category C where
  Hom := QHom (R := R)
  id := qid (R := R)
  comp := qcomp (R := R)
  id_comp := qid_comp (R := R)
  comp_id := qcomp_id (R := R)
  assoc := qassoc (R := R)

end RawCategoryModulo
end Kucera
