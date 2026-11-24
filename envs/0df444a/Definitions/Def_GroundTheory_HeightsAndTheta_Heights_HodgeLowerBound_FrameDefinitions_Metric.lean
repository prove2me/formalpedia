-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:50.032148+00:00
-- url     : https://prove2.me/theorems/d7c345a4-038f-4e08-9e96-f547c66280d1
-- title:
--   Metric
-- statement:
--   Definitions and structural lemmas for Metric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Values
variable {Ω : Type} [Field Ω]
open Classical in

def valAt (y : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ :=
  if h : ∃ v, IsValueAt y s z v then h.choose else 0
def chartMono (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ a k
def IsUnitOn (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f u : Ω) : Prop :=
  u ≠ 0 ∧ (∃ n : ℕ, f ^ n * u ∈ chartRing ℤ (segreCoord y) c) ∧
    ∃ n : ℕ, f ^ n * u⁻¹ ∈ chartRing ℤ (segreCoord y) c
end Values
section Orbits
def torusSetoid : Setoid ((Σ k, ι k) → ℂ) where
  r z z' := ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z
  iseqv := by
    refine ⟨fun z => ⟨1, fun _ => one_ne_zero, by funext p; simp [torusSmul]⟩, ?_, ?_⟩
    · rintro z z' ⟨c, hc, rfl⟩
      refine ⟨c⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
      funext p
      simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
    · rintro z z' z'' ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      refine ⟨d * c, fun k => mul_ne_zero (hd k) (hc k), ?_⟩
      funext p
      simp [torusSmul, mul_assoc]
def orbitRep (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  Quotient.out (Quotient.mk (torusSetoid (ι := ι)) z)
theorem orbitRep_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    orbitRep (torusSmul c z) = orbitRep z := by
  unfold orbitRep
  congr 1
  exact Quotient.sound ⟨c⁻¹, fun k => inv_ne_zero (hc k), by
    funext p; simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]⟩
end Orbits
section Lines
def refNorm (a : K → ℤ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ ((a k : ℝ) / 2)
theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) (a : ℤ) : (x ^ 2) ^ ((a : ℝ) / 2) = x ^ a := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx,
    show ((2 : ℕ) : ℝ) * ((a : ℝ) / 2) = ((a : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
theorem refNorm_smul (a : K → ℤ) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    refNorm a (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * refNorm a z := by
  unfold refNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : (∑ i, ‖torusSmul c z ⟨k, i⟩‖ ^ 2) = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [torusSmul, norm_mul, mul_pow]
  rw [this, Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    sq_rpow_half (norm_nonneg _)]
theorem refNorm_pos (a : K → ℤ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < refNorm a z := by
  refine Finset.prod_pos fun k _ => Real.rpow_pos_of_pos ?_ _
  obtain ⟨i, hi⟩ := hz k
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖)
    (Finset.mem_univ i))
variable (ι) in

def hermOfFun (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) : HermLine ι where
  a := a
  h z := refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z)))
  pos z hz := mul_pos (refNorm_pos a hz) (Real.exp_pos _)
  smul c z hc := by
    change refNorm a (torusSmul c z) * Real.exp (Real.log (F (orbitRep (torusSmul c z)) /
      refNorm a (orbitRep (torusSmul c z)))) = _
    rw [refNorm_smul, orbitRep_smul c hc, mul_assoc]
def IsHomogOfDeg (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z
end Lines
end GroundTheory.Heights₂.Heights.LowerBoundFree


