-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a84d9664-cb50-5980-9f12-8724695fb441

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicCurve.TwoChartIntegralModel

universe u

noncomputable section

namespace GenGluedK12

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem chartAlg_eq_chartRing (K₀ : Type u) [Field K₀] (F : Type u) [Field F] [Algebra K₀ F] (S : Set F) :
    chartAlg K₀ F S = CurveModel.chartRing K₀ S :=
  SetLike.ext fun _ => Iff.rfl

end GenGluedK12

open GenGluedK12 in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] :
    ∃ (es : AlgebraicCurve.CurveModel.glued K₀ j ⟶
        pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀))))
      (_ : IsIso es),
      es ≫ pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
          (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) =
        AlgebraicCurve.CurveModel.gluedToBase K₀ j := by
  obtain ⟨eFin', hFin⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg R K₀ F (nonZeroDivisors R) ({j} : Set F)
  obtain ⟨eInf', hInf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg R K₀ F (nonZeroDivisors R) ({j⁻¹} : Set F)
  let eFin : K₀ ⊗[R] ↥(chartAlgFin R F j) ≃ₐ[K₀] ↥(CurveModel.chartRing K₀ ({j} : Set F)) :=
    eFin'.trans (Subalgebra.equivOfEq _ _ (chartAlg_eq_chartRing K₀ F {j}))
  let eInf : K₀ ⊗[R] ↥(chartAlgInf R F j) ≃ₐ[K₀] ↥(CurveModel.chartRing K₀ ({j⁻¹} : Set F)) :=
    eInf'.trans (Subalgebra.equivOfEq _ _ (chartAlg_eq_chartRing K₀ F {j⁻¹}))
  have hcoeFin : ∀ x, ((eFin x : ↥(CurveModel.chartRing K₀ ({j} : Set F))) : F) = ((eFin' x : ↥(chartAlg K₀ F {j})) : F) :=
    fun _ => rfl
  have hcoeInf : ∀ x, ((eInf x : ↥(CurveModel.chartRing K₀ ({j⁻¹} : Set F))) : F) = ((eInf' x : ↥(chartAlg K₀ F {j⁻¹})) : F) :=
    fun _ => rfl
  have hj : ((eFin ((1 : K₀) ⊗ₜ[R] jChartFin R F j)) : F) = j := by
    rw [hcoeFin, hFin, one_smul]; rfl
  have hjInv : ((eInf ((1 : K₀) ⊗ₜ[R] jInvChartInf R F j)) : F) = j⁻¹ := by
    rw [hcoeInf, hInf, one_smul]; rfl
  have hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((eFin ((1 : K₀) ⊗ₜ[R] b)) : F) = ((eInf ((1 : K₀) ⊗ₜ[R] b')) : F) * j ^ n := by
    intro b b' n h
    rw [hcoeFin, hcoeInf, hFin, hInf, one_smul, one_smul, h]
  obtain ⟨es, hiso, hsnd, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
      R F j K₀ j eFin eInf hj hjInv hcompat
  exact ⟨es, hiso, hsnd⟩

end

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing (solution)
