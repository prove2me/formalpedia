-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
-- name    : OAI_Combinatorics_ExpectationThreshold_ScaleBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:31:31.861461+00:00
-- url     : https://prove2.me/theorems/cce67f00-0071-41b0-8408-79860fd02188
-- title:
--   The largest admissible scale
-- statement:
--   Let $\Sigma_s=\sum_{i<s}256^{\,i+1}$.
--
--   1. $\Sigma_s\ge s$ for all $s$.
--   2. For $p>0$ there is $s$ with $p\,\Sigma_{s+1}>\frac12$.
--   3. For $p>0$ the cutoff $s^*(p)$ is the least $s$ with
--   $$
--   p\,\Sigma_{s+1}>\tfrac12,
--   $$
--      and $s^*(p)=0$ for $p\le0$.
--
--   The cutoff is the largest number of scales the color law can afford at density $p$, since $p\Sigma_{s^*}\le\frac12$ by minimality. The next scale failing keeps the residual last color contribution small.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ScaleBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ScaleBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandExpectationThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The largest admissible scale

The cutoff is constructed as the first index whose next scale fails.
Its existence follows from the Archimedean property and the elementary
lower bound `scaleSum s ≥ s`. No finite search bound or computed large
power is used.
-/

namespace TalagrandThreshold

open scoped BigOperators

theorem scaleSum_ge_nat (s : ℕ) : (s : ℝ) ≤ scaleSum s := by
  calc
    (s : ℝ) = ∑ _i : Fin s, (1 : ℝ) := by simp
    _ ≤ scaleSum s := by
      unfold scaleSum
      exact Finset.sum_le_sum fun _ _ => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 256)

/-- Some next scale fails whenever the density is positive. -/
theorem scale_next_fail_exists {p : ℝ} (hp : 0 < p) :
    ∃ s : ℕ, 1 / 2 < p * scaleSum (s + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 / 2 : ℝ) / p)
  refine ⟨n, ?_⟩
  have hnp : (1 / 2 : ℝ) < (n : ℝ) * p := (div_lt_iff₀ hp).mp hn
  have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  calc
    (1 / 2 : ℝ) < p * (n : ℝ) := by simpa only [mul_comm] using hnp
    _ ≤ p * scaleSum (n + 1) :=
      mul_le_mul_of_nonneg_left (hcast.trans (scaleSum_ge_nat (n + 1))) hp.le

/-- The largest admissible scale; its irrelevant nonpositive-density value is zero. -/
noncomputable def maxScale (p : ℝ) : ℕ := by
  classical
  exact if hp : 0 < p then Nat.find (scale_next_fail_exists hp) else 0

end TalagrandThreshold

end OAI


