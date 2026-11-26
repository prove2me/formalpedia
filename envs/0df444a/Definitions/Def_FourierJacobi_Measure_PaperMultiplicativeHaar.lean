-- Prove2me | Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
-- name    : FourierJacobi_Measure_PaperMultiplicativeHaar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:52:57.33449+00:00
-- url     : https://prove2.me/theorems/d2de1b87-22b2-5f4e-9e4b-1260e3c0c475
-- title:
--   Paper Multiplicative Haar
-- statement:
--   Definitions and structural lemmas for Paper Multiplicative Haar, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/PaperMultiplicativeHaar.lean

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal
namespace FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
theorem paperMultiplicativeFactor_pos : 0 < 1 - (residueCardinality K : ℝ)⁻¹ := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  exact sub_pos.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq)
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]
def paperMultiplicativeHaar : MeasureTheory.Measure Kˣ :=
  ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) • multiplicativeHaar K
instance paperMultiplicativeHaar_isHaarMeasure : (paperMultiplicativeHaar K).IsHaarMeasure := by
  unfold paperMultiplicativeHaar
  exact Measure.IsHaarMeasure.smul (multiplicativeHaar K)
    (ENNReal.ofReal_pos.mpr (paperMultiplicativeFactor_pos K)).ne'
    ENNReal.ofReal_ne_top
instance paperMultiplicativeHaar_sigmaFinite : SigmaFinite (paperMultiplicativeHaar K) := by
  change SigmaFinite (Real.toNNReal (1 - (residueCardinality K : ℝ)⁻¹) • multiplicativeHaar K)
  infer_instance
end FourierJacobi.Measure


