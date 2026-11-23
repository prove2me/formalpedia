-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:31.277308+00:00
-- url     : https://prove2.me/theorems/8bfbb7eb-a3f9-4b82-99f3-b5506dff3a7d
-- title:
--   Split Torus Hom Eq One Of Nilpotent
-- statement:
--   Definitions and structural lemmas for Split Torus Hom Eq One Of Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace TorusNil
variable {A : Type} [CommRing A]
abbrev sp (A C : Type) [CommRing A] [CommRing C] [Algebra A C] : Over (Spec (CommRingCat.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A C)))
def spm {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D] (φ : C →ₐ[A] D) :
    sp A D ⟶ sp A C :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    simp only [Over.mk_left, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a; simp)
section
variable {C D E : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]
end
def triples (A : Type) [CommRing A] {C : Type} [CommRing C] [Algebra A C] (K : Ideal C) :
    Subalgebra A (C × C × C) where
  carrier := {t | t.1 - t.2.2 ∈ K ∧ t.2.1 - t.2.2 ∈ K}
  mul_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq, Prod.mk_mul_mk] at *
    constructor
    · have : a * a' - c * c' = a * (a' - c') + c' * (a - c) := by ring
      rw [this]; exact K.add_mem (K.mul_mem_left _ h3) (K.mul_mem_left _ h1)
    · have : b * b' - c * c' = b * (b' - c') + c' * (b - c) := by ring
      rw [this]; exact K.add_mem (K.mul_mem_left _ h4) (K.mul_mem_left _ h2)
  add_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq, Prod.mk_add_mk] at *
    constructor
    · have : a + a' - (c + c') = (a - c) + (a' - c') := by ring
      rw [this]; exact K.add_mem h1 h3
    · have : b + b' - (c + c') = (b - c) + (b' - c') := by ring
      rw [this]; exact K.add_mem h2 h4
  algebraMap_mem' r := by simp
section
variable {C : Type} [CommRing C] [Algebra A C] (K : Ideal C)
def tr₁ : triples A K →ₐ[A] C := (AlgHom.fst A C (C × C)).comp (triples A K).val
def tr₂ : triples A K →ₐ[A] C :=
  (AlgHom.fst A C C).comp ((AlgHom.snd A C (C × C)).comp (triples A K).val)
def tr₃ : triples A K →ₐ[A] C :=
  (AlgHom.snd A C C).comp ((AlgHom.snd A C (C × C)).comp (triples A K).val)
def trSum : triples A K →ₐ[A] C ⧸ K ^ 2 where
  toFun t := Ideal.Quotient.mk _ (t.1.1 + t.1.2.1 - t.1.2.2)
  map_one' := by simp
  map_zero' := by simp
  map_add' s t := by
    rw [← map_add]; congr 1
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add]; ring
  map_mul' := by
    rintro ⟨⟨a, b, c⟩, h1, h2⟩ ⟨⟨a', b', c'⟩, h3, h4⟩
    rw [← map_mul, Ideal.Quotient.eq]
    change a * a' + b * b' - c * c' - (a + b - c) * (a' + b' - c') ∈ K ^ 2
    have : a * a' + b * b' - c * c' - (a + b - c) * (a' + b' - c') =
      -((a - c) * (b' - c') + (b - c) * (a' - c')) := by ring
    rw [this, sq]
    exact neg_mem (add_mem (Ideal.mul_mem_mul h1 h4) (Ideal.mul_mem_mul h2 h3))
  commutes' r := by simp [← Ideal.Quotient.mk_algebraMap]
end
section
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)
end
section
variable (A) (X : Type) [AddCommGroup X]
def torusPt {C : Type} [CommRing C] [Algebra A C] (χ : Multiplicative X →* C) :
    sp A C ⟶ splitTorus (Spec (CommRingCat.of A)) X :=
  letI : Algebra (ULift.{0} ℤ) C := ULift.algebra' ℤ C
  (Over.homMk (V := (Over.pullback (toZ (Spec (CommRingCat.of A)))).obj
      ((Spec (CommRingCat.of C)).asOver (Spec (CommRingCat.of (ULift.{0} ℤ)))))
    (pullback.lift (𝟙 _) (sp A C).hom (specULiftZIsTerminal.hom_ext _ _))
      (pullback.lift_snd _ _ _)) ≫
    (Over.pullback (toZ (Spec (CommRingCat.of A)))).map
      (Spec.mapMulEquiv (R := ULift.{0} ℤ) (S := AddMonoidAlgebra (ULift.{0} ℤ) X) (T := C)
        (WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ)))
abbrev dm (g : X →+ X × X) : AddMonoidAlgebra A X →ₐ[A] AddMonoidAlgebra A (X × X) :=
  AddMonoidAlgebra.mapDomainAlgHom A A g
end
end TorusNil
end GlobalTheory


