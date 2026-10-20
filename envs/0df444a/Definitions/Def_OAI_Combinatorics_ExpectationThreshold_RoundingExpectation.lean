-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
-- name    : OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:28:24.312284+00:00
-- url     : https://prove2.me/theorems/d2640695-574e-4af9-98e0-0f93bda03018
-- title:
--   The subset-product score of a fractional cover
-- statement:
--   Let $X$ be finite, $g$ a function on subsets of $X$ and $Y:X\to\mathbb{R}$. The product score is
--   $$
--   Z_g(Y)=\sum_{\emptyset\ne S\subseteq X}g(S)\prod_{x\in S}Y(x).
--   $$
--
--   In the rounding argument $Y(x)$ is a decreasing function of the random color of $x$. A member with small mean color forces the score to be large, while independence keeps its expectation small.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingExpectation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingExpectation.lean by skeleton subtraction
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

namespace OAI

/-!
# The upper expectation bound for rounding

The score sums over nonempty subsets of the original ground set. Its moments
come from the actual coordinate product law. Nonemptiness saves a factor of
one fifth in the fractional-cover cost.
-/

open scoped BigOperators

namespace TalagrandThreshold

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The nonnegative subset-product score used by the rounding argument. -/
def productScore (g : Finset α → ℝ) (Y : α → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)), g S * ∏ x ∈ S, Y x

variable {Ω : Type*} [Fintype Ω]

end
end TalagrandThreshold

end OAI


