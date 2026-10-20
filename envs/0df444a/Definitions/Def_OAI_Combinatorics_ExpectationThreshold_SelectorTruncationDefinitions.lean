-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:32:34.392807+00:00
-- url     : https://prove2.me/theorems/b97e25f3-1c19-4bac-86c4-e62d2415bde7
-- title:
--   Heavy sets, truncated excess and admissible cutoffs
-- statement:
--   Let $X$ be finite, $w:X\to\mathbb{R}$ a weight, $A\subseteq X$, and $m,d,u\in\mathbb{R}$.
--
--   1. **Heavy set.** $\{x:w(x)>u\}$, using a strict cutoff.
--   2. **Truncated excess.**
--   $$
--   E_A(d,u)=\sum_{x\in X}\min(w(x),u)\bigl([x\in A]-(1-d)\bigr).
--   $$
--   3. **Admissible cutoff.** $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every heavy point lies in $A$, and $m\,u\le E_A(d,u)$.
--
--   The truncated excess measures how much more than a $1-d$ fraction of the (truncated) mass lies in $A$. Admissible cutoffs certify that a moved coloring keeps enough mass of a member in each prefix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationDefinitions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationDefinitions.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds

namespace OAI

/-!
# Finite weighted truncation

The heavy set uses a strict cutoff. Weights equal to the cutoff are already
saturated when the cutoff increases, as required by the maximal truncation
argument.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The points whose weight is strictly above the cutoff. -/
noncomputable def heavySet (w : α → ℝ) (u : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => u < w x)

/-- The excess mass after every coordinate is truncated at the same cutoff. -/
noncomputable def truncatedExcess (w : α → ℝ) (A : Finset α) (d u : ℝ) : ℝ :=
  ∑ x, min (w x) u * ((if x ∈ A then 1 else 0) - (1 - d))

/-- An admissible cutoff includes all heavy points and meets the truncated
weighted-excess test. -/
def Admissible (w : α → ℝ) (A : Finset α) (m d u : ℝ) : Prop :=
  0 ≤ u ∧ u ≤ 1 ∧ (∀ x, u < w x → x ∈ A) ∧
    m * u ≤ truncatedExcess w A d u

omit [DecidableEq α] in
@[simp] theorem mem_heavySet {w : α → ℝ} {u : ℝ} {x : α} :
    x ∈ heavySet w u ↔ u < w x := by
  classical
  simp [heavySet]

end TalagrandThreshold.Selector

end OAI


