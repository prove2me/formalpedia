-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:37:45.753581+00:00
-- url     : https://prove2.me/theorems/6275fa8f-f1aa-46d5-9475-ddefb7943f75
-- title:
--   Reindexing words preserves their profiles
-- statement:
--   Let $D,E,H$ be finite and $e:D\to E$ a bijection.
--
--   1. For every word $f:E\to H$, $\mathrm{prof}(f\circ e)=\mathrm{prof}(f)$.
--   2. Composition with $e$ is a bijection between the words on $D$ and the words on $E$ with a prescribed profile $n$:
--   $$
--   \{f:D\to H:\mathrm{prof}(f)=n\}\cong\{f:E\to H:\mathrm{prof}(f)=n\}.
--   $$
--
--   The number of words with a given profile therefore depends only on the size of the domain. This applies in particular to domains given as subsets of $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWordsTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWordsTransport.lean by skeleton subtraction
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

namespace OAI

/-!
# Transport of words with a prescribed profile

Reindexing the domain of a word preserves every letter count. Consequently,
the number of words with a prescribed profile depends only on the size of
the domain, including when that domain is the subtype of a finite set.
-/

namespace TalagrandThreshold

section Profile

variable {D E H : Type*} [Fintype D] [Fintype E] [DecidableEq H]

/-- A domain equivalence preserves the profile of a word. -/
theorem wordProfile_comp_equiv (e : D ≃ E) (f : E → H) :
    wordProfile (f ∘ e) = wordProfile f := by
  funext h
  change (Finset.univ.filter (fun i : D => f (e i) = h)).card =
    (Finset.univ.filter (fun j : E => f j = h)).card
  apply Finset.card_equiv e
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Profile

section Fiber

variable {D E H : Type*} [Fintype D] [Fintype E]
variable [DecidableEq D] [DecidableEq E] [Fintype H] [DecidableEq H]

/-- Reindexing gives an equivalence between words of the same profile. -/
def wordFiberEquiv (e : D ≃ E) (n : H → ℕ) :
    ↥(wordFiber D n) ≃ ↥(wordFiber E n) := by
  refine Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl H)) ?_
  intro f
  change f ∈ Finset.univ.filter (fun g : D → H => wordProfile g = n) ↔
    (f ∘ e.symm) ∈ Finset.univ.filter (fun g : E → H => wordProfile g = n)
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro hf
    exact ⟨Finset.mem_univ _, (wordProfile_comp_equiv e.symm f).trans hf.2⟩
  · intro hf
    exact ⟨Finset.mem_univ _, (wordProfile_comp_equiv e.symm f).symm.trans hf.2⟩

end Fiber

end TalagrandThreshold

end OAI


