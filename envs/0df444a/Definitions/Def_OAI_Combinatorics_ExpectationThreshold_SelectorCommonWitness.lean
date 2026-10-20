-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:43:02.656985+00:00
-- url     : https://prove2.me/theorems/1227b2f2-3a83-426a-8094-c5f6a1d5f44f
-- title:
--   A common feasibility witness for a profile group
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$, $P_i(z)=\{x:z(x)\le i\}$ and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$. A cutoff $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every $x$ with $w(x)>u$ lies in $A$, and $mu\le\sum_x\min(w(x),u)([x\in A]-(1-d))$. For a final coloring $z$ and a profile $n$, the group consists of the bad colorings $a$ that select $z$ with profile $n$.
--
--   A common witness for the group consists of a member $H$ and cutoffs $u_0,\dots,u_{s-1}$ such that:
--   1. for every $a$ in the group and every $i<s$, $u_i$ is admissible for $(\mu_H,P_i(z),\text{crossings}_i(a,z),d_i)$;
--   2. $u_i$ is the largest cutoff admissible with the profile crossing count of $n$ at $i$;
--   3. the heavy sets are small:
--   $$
--   \#\{x:\mu_H(x)>u_i\}\le2^{i+1}\,|n|,
--   $$
--      where $|n|$ is the total size of the profile;
--   4. every moved row $i$ of every $a$ in the group lies in the heavy set $\{x:\mu_H(x)>u_i\}$.
--
--   Within a group, admissibility depends on $a$ only through the profile. One member and one set of cutoffs therefore serve the whole group, and the moved rows are confined to small sets that do not depend on $a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCommonWitness.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCommonWitness.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay

namespace OAI

/-!
# One witness for an entire selector profile group

A nonempty group contains an actual selected move, hence an actual feasible
family member. Its admissibility tests depend on the original coloring only
through the full profile. Maximizing each cutoff for this one member therefore
produces common heavy sets for the entire group. Selected-move minimality puts
every moved row inside its corresponding common heavy set.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The same actual family member and cutoffs work for every original coloring
in a fixed final-coloring/profile group. -/
structure CommonWitness {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s) where
  member : ↥F
  cutoff : Fin s → ℝ
  admissible : ∀ a ∈ groupOriginals mu z n, ∀ i : Fin s,
    Admissible (mu.weight member) (prefixSet z i) (crossings a z i : ℝ)
      (dscale i) (cutoff i)
  maximal : ∀ (i : Fin s) (u : ℝ),
    Admissible (mu.weight member) (prefixSet z i) (profileCrossings n i : ℝ)
      (dscale i) u → u ≤ cutoff i
  card_le : ∀ i : Fin s,
    (heavySet (mu.weight member) (cutoff i)).card ≤ 2 ^ (i.val + 1) * profileSize n
  moved_subset : ∀ a ∈ groupOriginals mu z n, ∀ i : Fin s,
    movedRow a z i ⊆ heavySet (mu.weight member) (cutoff i)

end TalagrandThreshold.Selector

end

end OAI


