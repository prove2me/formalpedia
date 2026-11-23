-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- name    : GroundTheory_PAdicHodge_RobbaSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:16.784159+00:00
-- url     : https://prove2.me/theorems/7d1ff49f-71fb-4077-bdf8-ea016f05278f
-- title:
--   Robba Series
-- statement:
--   Definitions and structural lemmas for Robba Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean

import Mathlib
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
namespace GroundTheory.PAdicHodge
open Filter Topology
namespace Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
def ConvergesAt (a : ℤ → K) (ρ : ℝ) : Prop :=
  Tendsto (fun n : ℤ => ‖a n‖ * ρ ^ n) cofinite (𝓝 0)
def cmul (a b : ℤ → K) : ℤ → K := fun n => ∑' i, a i * b (n - i)
def gaussNorm (a : ℤ → K) (ρ : ℝ) : ℝ := ⨆ n, ‖a n‖ * ρ ^ n
def domSet (a : ℤ → K) (ρ : ℝ) : Set ℤ := {n | ‖a n‖ * ρ ^ n = gaussNorm a ρ}
def lowIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sInf (domSet a ρ)
def highIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sSup (domSet a ρ)
variable {a b c : ℤ → K} {ρ : ℝ}
section Basic
end Basic
section Product
theorem norm_mul_term (hρ : ρ ≠ 0) (n i : ℤ) :
    ‖a i * b (n - i)‖ = (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) / ρ ^ n := by
  rw [norm_mul, eq_div_iff (zpow_ne_zero _ hρ)]
  have : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ]; congr 1; ring
  rw [this]; ring
theorem tendsto_weight_prod (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    Tendsto (fun p : ℤ × ℤ => (‖a p.1‖ * ρ ^ p.1) * (‖b p.2‖ * ρ ^ p.2)) cofinite (𝓝 0) :=
  tendsto_mul_cofinite_nhds_zero ha hb
theorem norm_cmul_mul_zpow_le (hρ : 0 < ρ) {n : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) ≤ C) :
    ‖cmul a b n‖ * ρ ^ n ≤ C := by
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← le_div_iff₀ hρn]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hC hρn.le) fun i => ?_
  rw [norm_mul_term hρ.ne' n i]
  exact div_le_div_of_nonneg_right (h i) hρn.le
theorem ConvergesAt.cmul (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    ConvergesAt (cmul a b) ρ := by
  have hw := tendsto_weight_prod ha hb
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n =>
    lt_of_lt_of_le hx (by positivity), fun ε hε => ?_⟩
  have hS : {p : ℤ × ℤ | ε / 2 ≤ (‖a p.1‖ * ρ ^ p.1) * (‖b p.2‖ * ρ ^ p.2)}.Finite := by
    have := Filter.eventually_cofinite.1 (hw.eventually (gt_mem_nhds (half_pos hε)))
    simpa only [not_lt] using this
  refine Filter.eventually_cofinite.2 ((hS.image fun p => p.1 + p.2).subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hn
  by_contra hcon
  have : ‖Laurent.cmul a b n‖ * ρ ^ n ≤ ε / 2 := norm_cmul_mul_zpow_le hρ (by positivity) fun i => by
    by_contra h'
    exact hcon ⟨(i, n - i), (not_le.1 h').le, by simp⟩
  linarith
variable [CompleteSpace K]
end Product
section Dominant
section Attained
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha
end Attained
section Multiplicative
variable [CompleteSpace K]
variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0
end Multiplicative
end Dominant
end Laurent
end GroundTheory.PAdicHodge


