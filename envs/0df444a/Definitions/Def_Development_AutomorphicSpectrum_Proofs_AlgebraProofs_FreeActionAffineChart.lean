-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
-- name    : Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:09.188247+00:00
-- url     : https://prove2.me/theorems/c1f3a225-5477-4838-8adb-52d40d16c4ad
-- title:
--   Free Action Affine Chart
-- statement:
--   Definitions and structural lemmas for Free Action Affine Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FreeActionAffineChart.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul


set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory.AffineQuotient
open TensorProduct Algebra.TensorProduct
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
set_option backward.isDefEq.respectTransparency false
abbrev modObjObj {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (M X : C) [MonObj M] [ModObj M X] :
    letI := Functor.monObjObj (F := F) (X := M); ModObj (F.obj M) (F.obj X) :=
  letI := Functor.monObjObj (F := F) (X := M)
  { smul := Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]
    one_smul := by
      change (Functor.LaxMonoidal.ε F ≫ F.map η[M]) ▷ F.obj X ≫ Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] = (λ_ (F.obj X)).hom
      rw [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
        ModObj.one_smul_self, Functor.LaxMonoidal.left_unitality]
    mul_smul := by
      change (Functor.LaxMonoidal.μ F M M ≫ F.map μ[M]) ▷ F.obj X ≫ Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] =
        (α_ _ _ _).hom ≫ F.obj M ◁ (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]) ≫ Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]
      rw [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
        ModObj.mul_smul_self, whiskerLeft_comp, Category.assoc,
        Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp, F.map_comp, F.map_comp]
      simp [Functor.LaxMonoidal.associativity_assoc] }
lemma comp_inv'' {C : Type*} [Category C] [CartesianMonoidalCategory C] {A : C} [GrpObj A] {T T' : C}
    (r : T' ⟶ T) (x : T ⟶ A) : r ≫ x⁻¹ = (r ≫ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])
section Affine
variable {R : Type} [CommRing R]
section Coaction
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
variable {H Z : Over (Spec (CommRingCat.of R))} [GrpObj H] [ModObj H Z]
variable (i : specOver R Λ ⟶ H) (v : specOver R B ⟶ Z) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
    (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v))
include hρ
end Coaction
def invIso (H : Over (Spec (CommRingCat.of R))) [GrpObj H] : H ≅ H where
  hom := ι[H]
  inv := ι[H]
  hom_inv_id := by
    have h : ι[H] = (𝟙 H)⁻¹ := by rw [Hom.inv_def]; simp
    rw [h, comp_inv'', Category.comp_id, inv_inv]
  inv_hom_id := by
    have h : ι[H] = (𝟙 H)⁻¹ := by rw [Hom.inv_def]; simp
    rw [h, comp_inv'', Category.comp_id, inv_inv]
end Affine
section Open
variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]
end Open
section Base
variable {S S' : Scheme.{0}} (j : S' ⟶ S)
end Base
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart


