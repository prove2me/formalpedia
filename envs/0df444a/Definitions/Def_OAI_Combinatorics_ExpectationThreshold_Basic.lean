-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
-- name    : OAI_Combinatorics_ExpectationThreshold_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:21:10.335837+00:00
-- url     : https://prove2.me/theorems/a04484a2-ed6c-4897-a7a4-3250ac5b0655
-- title:
--   Basic facts about costs, covers and fractional covers
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A family $\mathcal{G}$ covers $\mathcal{F}$ if every $H\in\mathcal{F}$ contains some $S\in\mathcal{G}$; its cost at density $p$ is $\sum_{S\in\mathcal{G}}p^{|S|}$, and $\mathcal{F}$ is $p$-small if some cover has cost at most $\frac12$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ such that $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost is $\sum_{S\subseteq X}g(S)p^{|S|}$.
--
--   1. The empty family has cost $0$, a single set $S$ has cost $p^{|S|}$, and every family covers the empty family.
--   2. The cover indicator of $\mathcal{G}$ is the $0/1$-valued function $S\mapsto[S\in\mathcal{G}]$, which views an integral cover as a fractional one.
--   3. A fractional cover is nonnegative, and for $p\ge0$ the weight of the empty set is at most the fractional cost:
--   $$
--   g(\emptyset)\le\sum_Sg(S)p^{|S|}.
--   $$
--
--   In particular a fractional cover of cost at most $\frac12$ has $g(\emptyset)\le\frac12$, so its covering condition must be met by nonempty subsets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/Basic.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_empty (p : ℝ) : cost p (∅ : Family α) = 0 := by
  simp [cost]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_singleton (p : ℝ) (S : Finset α) :
    cost p {S} = p ^ S.card := by simp [cost]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem covers_empty (G : Family α) : Covers G ∅ := by
  intro H hH
  exact False.elim (Finset.notMem_empty H hH)

def coverIndicator (G : Family α) (S : Finset α) : ℝ := if S ∈ G then 1 else 0

omit [Fintype α] [DecidableEq α] in
theorem FractionalCover.nonneg {F : Family α} {g : Finset α → ℝ}
    (h : FractionalCover F g) (S : Finset α) : 0 ≤ g S := (h.1 S).1

omit [DecidableEq α] in
theorem empty_weight_le_fracCost {p : ℝ} {g : Finset α → ℝ}
    (hp : 0 ≤ p) (hg : ∀ S, 0 ≤ g S) : g ∅ ≤ fracCost p g := by
  have h := Finset.single_le_sum
    (fun S (_ : S ∈ (Finset.univ : Finset (Finset α))) =>
      mul_nonneg (hg S) (pow_nonneg hp S.card))
    (Finset.mem_univ (∅ : Finset α))
  simpa only [fracCost, Finset.card_empty, pow_zero, mul_one] using h

end
end TalagrandThreshold

end OAI


