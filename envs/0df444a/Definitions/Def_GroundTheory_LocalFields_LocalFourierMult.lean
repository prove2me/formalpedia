-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
-- name    : GroundTheory_LocalFields_LocalFourierMult
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:37.59634+00:00
-- url     : https://prove2.me/theorems/ffc117bc-8bae-4901-9883-06b560f274a6
-- title:
--   Local Fourier Mult
-- statement:
--   Definitions and structural lemmas for Local Fourier Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Theorems.Thm_GroundTheory_LocalField_coe_valBall_zero
import Theorems.Thm_GroundTheory_LocalField_eq_smul_haarIntegers
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
instance borelSpace_units : BorelSpace Kˣ :=
  measurableEmbedding_units_val.borelSpace isOpenEmbedding_units_val.isInducing
def unitsMeasureOf (μ : Measure K) : Measure Kˣ :=
  Measure.comap Units.val (μ.withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹)
def multHaarOf (μ : Measure K) : Measure Kˣ := multHaarConst K • unitsMeasureOf μ
theorem multHaarOf_haarIntegers : multHaarOf (haarIntegers K) = multHaar K := by
  rw [multHaarOf, unitsMeasureOf, multHaar, Measure.comap_smul]
omit [BorelSpace K] in
theorem unitsMeasureOf_smul (c : ℝ≥0∞) (μ : Measure K) :
    unitsMeasureOf (c • μ) = c • unitsMeasureOf μ := by
  rw [unitsMeasureOf, unitsMeasureOf, withDensity_smul_measure, Measure.comap_smul]
omit [BorelSpace K] in
theorem multHaarOf_smul (c : ℝ≥0∞) (μ : Measure K) : multHaarOf (c • μ) = c • multHaarOf μ := by
  rw [multHaarOf, multHaarOf, unitsMeasureOf_smul, smul_comm]
theorem multHaarOf_eq (μ : Measure K) [μ.IsAddHaarMeasure] :
    multHaarOf μ = μ (𝒪[K] : Set K) • multHaar K := by
  conv_lhs => rw [eq_smul_haarIntegers μ]
  rw [multHaarOf_smul, multHaarOf_haarIntegers]
instance (μ : Measure K) [μ.IsAddHaarMeasure] : (multHaarOf μ).IsHaarMeasure := by
  rw [multHaarOf_eq μ]
  have h0 : μ (𝒪[K] : Set K) ≠ 0 := by
    rw [← coe_valBall_zero]
    exact (isOpen_valBall 0).measure_ne_zero μ ⟨0, zero_mem _⟩
  have ht : μ (𝒪[K] : Set K) ≠ ∞ := by
    rw [← coe_valBall_zero]
    exact (isCompact_valBall 0).measure_lt_top.ne
  exact IsHaarMeasure.smul _ h0 ht
namespace Padic
variable (p : ℕ) [Fact p.Prime] (K) [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]
end Padic
end GroundTheory.LocalField


