-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:34.474996+00:00
-- url     : https://prove2.me/theorems/f393d0a8-9acf-4df6-80ef-b7865b38fc77
-- title:
--   PReg Lelong Annulus
-- statement:
--   Definitions and structural lemmas for PReg Lelong Annulus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace RegLelongAnnulus
section Chart
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
variable (hCM : ChartMassCompact.Statement) (hJ : J.IsPrime)
  (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (m : ℕ)) (hA : IsFiniteProjection J A)
include hCM hJ hdim hA
end Chart
section Radial
def pk (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 1) / 2
def qk (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 1) / 4
theorem inv_succ_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := by positivity
theorem inv_succ_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 :=
  (div_le_one (by positivity)).2 (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
theorem half_le_pk (k : ℕ) : 1 / 2 ≤ pk k := by
  have := inv_succ_le_one k
  unfold pk
  linarith
theorem pk_pos (k : ℕ) : 0 < pk k := lt_of_lt_of_le (by norm_num) (half_le_pk k)
theorem pk_lt_qk (k : ℕ) : pk k < qk k := by
  have := inv_succ_pos k
  unfold pk qk
  linarith
def hk (k : ℕ) : ContDiffBump (0 : ℝ) := ⟨pk k, qk k, pk_pos k, pk_lt_qk k⟩
def Ik (e k : ℕ) : ℝ := ∫ w in (0 : ℝ)..1, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1))
end Radial
section Ball
variable {n : ℕ} (x : Fin n → ℂ)
def bigBump (s : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨s ^ 2 + 1, 2 * (s ^ 2 + 1), by positivity, by nlinarith [sq_nonneg s]⟩
def majorant (s : ℝ) (z : Fin n → ℂ) : ℝ := bigBump s (euclPot (z - x))
def smallBump {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r ^ 2 / 8, r ^ 2 / 4, by positivity, by have := pow_pos hr 2; linarith⟩
def logDistSmooth {r : ℝ} (hr : 0 < r) (z : Fin n → ℂ) : ℝ :=
  Real.log (euclPot (z - x) + r ^ 2 * smallBump hr (euclPot (z - x)))
end Ball
section Weights
variable {r s : ℝ} (e : ℕ)
def annWeight (r s : ℝ) (e k : ℕ) (t : ℝ) : ℝ :=
  r ^ (2 * (e + 1)) * hk k (t / s ^ 2) - s ^ (2 * (e + 1)) * hk k (t / r ^ 2)
variable {n : ℕ} (x : Fin n → ℂ)
end Weights
end RegLelongAnnulus
end
end GroundTheory.Heights₂.Heights


