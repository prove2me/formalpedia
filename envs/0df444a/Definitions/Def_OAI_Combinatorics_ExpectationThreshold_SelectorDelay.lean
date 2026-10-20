-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorDelay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:42:27.917546+00:00
-- url     : https://prove2.me/theorems/394cf03b-ea58-404f-b6f2-1ba68e94d19e
-- title:
--   Delaying one moved point by one color
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$, $P_i(z)=\{x:z(x)\le i\}$ and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$. A cutoff $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every $x$ with $w(x)>u$ lies in $A$, and $mu\le\sum_x\min(w(x),u)([x\in A]-(1-d))$. For a coloring $z$, a point $x$ and $i<s$, the delayed coloring is
--   $$
--   z'=z\text{ with }z'(x)=i+1 .
--   $$
--
--   If $x$ has final color $i$ and was moved, delaying it removes exactly $x$ from the prefix at $i$, leaves all other prefixes unchanged, and lowers the movement by one. This is the step used to show that selected moves have their moved rows inside heavy sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelay.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelay.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound

namespace OAI

/-!
# Delaying one moved coordinate by one color

When a moved coordinate has final color `i`, replacing it by `i.succ` removes
exactly that coordinate from the prefixSet at cut `i`. Every other cut stays
unchanged, and total movement decreases by one.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

/-- Raise the final color of `x` to the color immediately after cut `i`. -/
def delayColor (z : Coloring α s) (x : α) (i : Fin s) : Coloring α s :=
  Function.update z x i.succ

omit [Fintype α] in
@[simp] theorem delayColor_apply_self (z : Coloring α s) (x : α) (i : Fin s) :
    delayColor z x i x = i.succ := by
  simp [delayColor]

end TalagrandThreshold.Selector

end

end OAI


