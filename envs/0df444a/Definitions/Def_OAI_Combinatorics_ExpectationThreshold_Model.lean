-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
-- name    : OAI_Combinatorics_ExpectationThreshold_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:19:19.073872+00:00
-- url     : https://prove2.me/theorems/17764beb-7d9a-4fab-9578-013add5b1c06
-- title:
--   Integral and fractional feasibility of densities
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A family $\mathcal{G}$ covers $\mathcal{F}$ if every $H\in\mathcal{F}$ contains some $S\in\mathcal{G}$; its cost at density $p$ is $\sum_{S\in\mathcal{G}}p^{|S|}$, and $\mathcal{F}$ is $p$-small if some cover has cost at most $\frac12$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ such that $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost is $\sum_{S\subseteq X}g(S)p^{|S|}$. The integral and fractional expectation thresholds are
--   $$
--   q(\mathcal{F})=\sup\{p\in[0,1]:\mathcal{F}\text{ is }p\text{-small}\},\qquad q_f(\mathcal{F})=\sup\{p\in[0,1]:\mathcal{F}\text{ has a fractional cover of cost}\le\tfrac12\}.
--   $$
--
--   The members recorded here are the membership rules for the two feasible sets: $p$ is integrally feasible iff $0\le p\le1$ and $\mathcal{F}$ is $p$-small, and fractionally feasible iff $0\le p\le1$ and $\mathcal{F}$ is fractionally $p$-small. Fractional covers range over every subset of $X$, including the empty set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/Model.lean by skeleton subtraction
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

namespace OAI

/-!
# Containment covers and expectation thresholds

Both costs use budget one half. Fractional coefficients are indexed by every
subset of the ground set, without a support-size bound. The empty subset is
included, and ordinary natural powers give `p^0 = 1`, including at zero.
The thresholds are real suprema of feasible densities in the closed unit interval.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
@[simp] theorem mem_integralFeasible {F : Family α} {p : ℝ} :
    p ∈ integralFeasible F ↔ 0 ≤ p ∧ p ≤ 1 ∧ Small p F := Iff.rfl

omit [DecidableEq α] in
@[simp] theorem mem_fractionalFeasible {F : Family α} {p : ℝ} :
    p ∈ fractionalFeasible F ↔ 0 ≤ p ∧ p ≤ 1 ∧ FractionalSmall p F := Iff.rfl

end
end TalagrandThreshold

end OAI


