-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinLine
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:28.87706+00:00
-- url     : https://prove2.me/theorems/cde0f80e-5b0b-4c6a-b6a2-2b1690511276
-- title:
--   Dixmier Malliavin Line
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
namespace LineKernel
def radii (ε : ℝ) (j : ℕ) : ℝ := ε / 2 ^ (j + 3)
theorem radii_pos {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 < radii ε j := by unfold radii; positivity
def weight (M : ℕ → ℝ) (p : ℕ) : ℝ := if p = 0 then 1 else (1 / 2) ^ p / max 1 |M p|
def Good (M : ℕ → ℝ) (ε : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  0 < x ∧ (∀ p ∈ Finset.range (j + 2), 1 ≤ p →
      x⁻¹ * weight M (p - 1) ≤ (1 / 2) ^ (j + 1) * weight M p) ∧
    (∀ q ∈ Finset.range (2 * j + 3), ∀ t,
      ‖iteratedDeriv q (rem x (radii ε j)) t‖ ≤ (1 / 2) ^ j / (j + 2)) ∧
    exp (-x * radii ε j) ≤ (1 / 2) ^ j
section Sequence
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
theorem exists_bound_iteratedDeriv_ρ (k j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ C := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hc : HasCompactSupport (ρ a (radii ε) j) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_ρ_subset ha hr j)
  obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv hc k).exists_bound_of_continuous
    ((contDiff_ρ ha hr j).continuous_iteratedDeriv k (by exact_mod_cast le_top))
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩
def majorant (k j : ℕ) : ℝ :=
  (1 / 2) ^ j + if j ≤ k then (exists_bound_iteratedDeriv_ρ hε hg k j).choose else 0
def remSum (t : ℝ) : ℂ := ∑' j, ρ a (radii ε) j t
end Sequence
section Limit
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
def climit (p : ℕ) : ℝ := ⨆ n, coef a n p
end Limit
end LineKernel
end
end GroundTheory.Automorphic


