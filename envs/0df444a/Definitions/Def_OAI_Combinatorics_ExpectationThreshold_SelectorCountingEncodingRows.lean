-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:38:51.943997+00:00
-- url     : https://prove2.me/theorems/dc03bbbe-e84f-4dc6-8148-253860e8ac73
-- title:
--   Row encodings with a prescribed size and profile
-- statement:
--   Let $X$ and $H$ be finite, $R\subseteq X$, $t\in\mathbb{N}$, and $n:H\to\mathbb{N}$ a profile. A row encoding consists of a subset $U\subseteq R$ with $|U|=t$ together with a word on $U$ of profile $n$:
--   $$
--   \mathrm{Enc}(R,t,n)=\{(U,f):\ U\subseteq R,\ |U|=t,\ f:U\to H,\ \mathrm{prof}(f)=n\}.
--   $$
--
--   The set of encodings is finite. Its size factors as $\binom{|R|}{t}$ times the word count of $n$ on $t$ letters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingRows.lean by skeleton subtraction
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

namespace OAI

/-!
# Counting row encodings

A row encoding chooses a subset of the available positions and labels those
positions with a word of a prescribed profile. The word count depends only on
the number of chosen positions, so the total count factors into a binomial
coefficient and the corresponding word count.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α H : Type*} [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]

/-- A chosen set of positions together with labels of the prescribed profile. -/
def RowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) : Type _ :=
  Σ U : {U : Finset α // U ⊆ R ∧ U.card = t}, ↥(wordFiber ↥U.val n)

noncomputable instance instFintypeRowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) :
    Fintype (RowEncoding R t n) :=
  inferInstanceAs (Fintype
    (Σ U : {U : Finset α // U ⊆ R ∧ U.card = t}, ↥(wordFiber ↥U.val n)))

end TalagrandThreshold

end OAI


