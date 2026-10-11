-- Prove2me | solution 1 for AsymptoticOperator.exists_coeff_eq_coeffMul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T12:09:13.664101+00:00
-- url     : https://prove2.me/submissions/dbc5bda8-f074-4ea5-b220-a6ceba42d0e7

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.Analysis.CStarAlgebra.Matrix

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (f : L2 n) :
    ∃ m : L2 n, ∀ k : ℤ, coeff m k = coeffMul S f k := by
  let E := toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)
  have hE : Continuous fun A : Mat n => E A :=
    LinearMap.continuous_of_finiteDimensional E.toAlgEquiv.toLinearMap
  let T : C(UnitAddCircle, Vec n →L[ℝ] Vec n) := ⟨fun t => E (S t), hE.comp S.continuous⟩
  have hmeas : AEStronglyMeasurable (fun t => T t (f t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    have hc : Continuous fun p : (Vec n →L[ℝ] Vec n) × Vec n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hc.comp_aestronglyMeasurable
      (T.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f))
  have hmem : MemLp (fun t => T t (f t)) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (Lp.memLp f).of_le_mul hmeas (ae_of_all _ fun t =>
      ((T t).le_opNorm (f t)).trans
        (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm t) (norm_nonneg _)))
  refine ⟨hmem.toLp _, fun k => ?_⟩
  simp only [coeff, coeffMul]
  refine congrFun (fourierCoeff_congr_ae ?_) k
  filter_upwards [hmem.coeFn_toLp] with t ht
  rw [ht]
  funext i
  simp only [T, E, ContinuousMap.coe_mk, complexify]
  change ((((S t) *ᵥ ((f t : Vec n) : Fin n ⊕ Fin n → ℝ)) i : ℝ) : ℂ) = _
  simp [mulVec, dotProduct, complexify]
