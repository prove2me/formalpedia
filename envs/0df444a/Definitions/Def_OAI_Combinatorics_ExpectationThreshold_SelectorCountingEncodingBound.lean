-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:41:39.879621+00:00
-- url     : https://prove2.me/theorems/7f2c07f2-4916-401b-a327-f3450cd66e38
-- title:
--   The profile row encoding of a coloring
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,1,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$ the prefix of a coloring $z$ is $P_i(z)=\{x:z(x)\le i\}$, and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$. For colorings $a,z$ and a profile $n$, suppose $n_{a,z}=n$, and let $R_i\supseteq$ the moved row $i$ for every $i$.
--
--   1. Restricting a labelling to a finite set $U$ has profile counting the fibres within $U$; in particular the original colors on the moved row $i$ have profile $n(i,\cdot)$.
--   2. The profile row encoding of row $i$ is the moved row (a subset of $R_i$ of size $\sum_hn(i,h)$) together with the original colors on it, which is an element of
--   $$
--   \mathrm{Enc}\Bigl(R_i,\ \sum_hn(i,h),\ n(i,\cdot)\Bigr).
--   $$
--   3. Forgetting the constraints recovers the raw row record.
--
--   Since the rows and their labels determine $a$, this gives an injection from a profile group into a product of row encodings. The size of the group is bounded by products of binomial and word counts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingBound.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingBound.lean by skeleton subtraction
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

namespace OAI

/-!
# The fixed-profile encoding bound

Each actual coloring maps to the tuple of its changed row subsets and the
original colors on them. Reconstruction proves this map injective. The row
record permits arbitrary subsets of the fixed ambient sets, so overlap between
those ambient sets can only enlarge the number of records.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [Fintype α] [DecidableEq α] in
/-- Restricting a labeling to a finite set counts exactly its fibers there. -/
theorem wordProfile_restrict_finset {H : Type*} [DecidableEq H]
    (U : Finset α) (f : α → H) (h : H) :
    wordProfile (fun x : ↥U => f x.val) h =
      (U.filter fun x => f x = h).card := by
  unfold wordProfile
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

omit [DecidableEq α] in
/-- The recorded original labels have precisely the actual profile row. -/
theorem movedRow_wordProfile (a z : Coloring α s) (i : Fin s) :
    wordProfile (fun x : ↥(movedRow a z i) => a x.val) = profile a z i := by
  funext h
  rw [wordProfile_restrict_finset, profile_eq_card_filter_movedRow]

/-- The literal row record with its proved size and histogram constraints. -/
def profileRowEncoding (a z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α) (hn : profile a z = n)
    (hR : ∀ i, movedRow a z i ⊆ R i) (i : Fin s) :
    RowEncoding (R i) (rowCount n i) (n i) :=
  ⟨⟨movedRow a z i, hR i, by rw [movedRow_card_eq_rowCount, hn]⟩,
    ⟨fun x => a x.val, (mem_wordFiber _ _ _).mpr
      ((movedRow_wordProfile a z i).trans (congrFun hn i))⟩⟩

/-- Forgetting the constraints retains the actual changed subset and labels. -/
def rowEncodingForget {R : Finset α} {t : ℕ} {n : Color s → ℕ}
    (E : RowEncoding R t n) : RawRowEncoding α s :=
  ⟨E.1.val, E.2.val⟩

@[simp] theorem rowEncodingForget_profileRowEncoding
    (a z : Coloring α s) (n : Profile s) (R : Fin s → Finset α)
    (hn : profile a z = n) (hR : ∀ i, movedRow a z i ⊆ R i) (i : Fin s) :
    rowEncodingForget (profileRowEncoding a z n R hn hR i) =
      rawRowEncoding a z i := rfl

end TalagrandThreshold.Selector

end

end OAI


