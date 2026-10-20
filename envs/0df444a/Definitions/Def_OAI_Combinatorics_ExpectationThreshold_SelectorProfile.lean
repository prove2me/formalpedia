-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorProfile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:40:02.257001+00:00
-- url     : https://prove2.me/theorems/82f1b67a-1b04-4d56-9ac4-2d470d216b9e
-- title:
--   Profile entries count original colors within moved rows
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,1,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$ the prefix of a coloring $z$ is $P_i(z)=\{x:z(x)\le i\}$, and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$. For colorings $a,z$, the profile entry $n_{a,z}(i,h)$ counts the points with final color $i$ and original color $h>i$.
--
--   1. $n_{a,z}(i,h)$ is the number of points of the moved row $i$ whose original color is $h$.
--   2. Summing over $h$ gives the size of the moved row:
--   $$
--   \sum_hn_{a,z}(i,h)=\#\{x:z(x)=i<a(x)\}.
--   $$
--   3. $a$ lies in the group of $(z,n)$ iff $a$ is bad, $z$ is selected for $a$, and $n_{a,z}=n$.
--
--   These counts hold without assuming that $z$ is earlier than $a$, since every counted point moves downward.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorProfile.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorProfile.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Exact counts in a selector profile

The full profile records each strict downward move by its final and original
colors. These counting identities hold even without a global `Earlier`
hypothesis: every point counted by a crossing already moves downward.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- A profile entry is the original-color fiber within its moved row. -/
theorem profile_eq_card_filter_movedRow (a z : Coloring α s)
    (i : Fin s) (h : Color s) :
    profile a z i h = ((movedRow a z i).filter fun x => a x = h).card := by
  unfold profile movedRow
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hz, ha, hi⟩
    exact ⟨⟨hz, by simpa only [hz, ha] using hi⟩, ha⟩
  · rintro ⟨⟨hz, hi⟩, ha⟩
    exact ⟨hz, ha, by simpa only [hz, ha] using hi⟩

omit [DecidableEq α] in
/-- All original colors partition the moved row. -/
theorem rowCount_profile (a z : Coloring α s) (i : Fin s) :
    rowCount (profile a z) i = (movedRow a z i).card := by
  unfold rowCount
  simp_rw [profile_eq_card_filter_movedRow]
  simpa using Finset.sum_card_fiberwise_eq_card_filter
    (movedRow a z i) Finset.univ a

omit [DecidableEq α] in
theorem movedRow_card_eq_rowCount (a z : Coloring α s) (i : Fin s) :
    (movedRow a z i).card = rowCount (profile a z) i :=
  (rowCount_profile a z i).symm

@[simp] theorem mem_groupOriginals {F : Family α} (mu : MassFamily F)
    (a z : Coloring α s) (n : Profile s) :
    a ∈ groupOriginals mu z n ↔ Bad mu a ∧ Selected mu a z ∧ profile a z = n := by
  classical
  simp only [groupOriginals, Finset.mem_filter, Finset.mem_univ, true_and]

end TalagrandThreshold.Selector

end

end OAI


