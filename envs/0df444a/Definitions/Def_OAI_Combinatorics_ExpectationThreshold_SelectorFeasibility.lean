-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:34:48.412979+00:00
-- url     : https://prove2.me/theorems/190c67c5-aedd-4972-b56e-99472b872d7e
-- title:
--   Resetting a member and the selected cover
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,1,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$ the prefix of a coloring $z$ is $P_i(z)=\{x:z(x)\le i\}$, and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$.
--
--   1. **Reset.** For a coloring $a$ and a member $H_0$, the reset coloring gives color $0$ on $H_0$ and agrees with $a$ elsewhere:
--   $$
--   a^{H_0}(x)=\begin{cases}0,&x\in H_0,\\a(x),&x\notin H_0.\end{cases}
--   $$
--   2. **Selected moves.** $z$ belongs to the selected moves of $a$ exactly when it is selected for $a$.
--   3. **Selected changes.** The family of changed sets $\{x:z(x)<a(x)\}$ of the selected moves.
--
--   Resetting a member gives a bounded feasible move, so minimal moves exist. Their changed sets cover every member of the family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorFeasibility.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorFeasibility.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Feasible minima and the actual containment cover

Resetting an original family member to the first color proves existence of
a bounded feasible move. Minimization itself retains the unrestricted
feasibility witness from `Feasible`; the witness need not be that member.
All retained minima contribute their actual changed sets to a cover.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- Reset only the specified member to zero, the first color index. -/
def reset (a : Coloring α s) (H₀ : ↥F) : Coloring α s :=
  fun x => if x ∈ H₀.val then 0 else a x

@[simp] theorem mem_selectedMoves {mu : MassFamily F} {a z : Coloring α s} :
    z ∈ selectedMoves mu a ↔ Selected mu a z := by
  classical
  simp [selectedMoves]

/-- Remove duplicate changed sets only when forming the containment cover. -/
def selectedChanges (mu : MassFamily F) (a : Coloring α s) : Family α := by
  classical
  exact (selectedMoves mu a).image (changes a)

end TalagrandThreshold.Selector

end

end OAI


