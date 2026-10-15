-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:21:11.726907+00:00
-- url     : https://prove2.me/theorems/e853830e-a632-4f17-8275-ce6175136b68
-- title:
--   The continuum as a well-ordered index set, and unions of fewer than continuum many finite sets
-- statement:
--   Write $\mathfrak c=2^{\aleph_0}$ for the cardinality of the continuum and $\operatorname{ord}(\kappa)$ for the initial ordinal of a cardinal $\kappa$ (the least ordinal of cardinality $\kappa$). This file fixes the well-ordered index set used by the continuum-length constructions and records the cardinal arithmetic they need.
--
--   1. **The continuum index set.** $\mathcal C$ is a well-ordered set of order type $\operatorname{ord}(\mathfrak c)$, i.e. a copy of the set of ordinals below $\operatorname{ord}(\mathfrak c)$. It satisfies
--   $$|\mathcal C|=\mathfrak c,\qquad \operatorname{otp}(\mathcal C,<)=\operatorname{ord}\bigl(|\mathcal C|\bigr),\qquad \bigl|\{j\in\mathcal C:\ j<i\}\bigr|<\mathfrak c\quad\text{for every } i\in\mathcal C,$$
--   so every index has fewer than $\mathfrak c$ predecessors.
--   2. **Fewer than continuum many finite sets.** Let $\iota$ and $\alpha$ be sets with $|\iota|<\mathfrak c$. If $(F_i)_{i\in\iota}$ is a family of finite subsets of $\alpha$, then
--   $$\Bigl|\bigcup_{i\in\iota}F_i\Bigr|<\mathfrak c .$$
--   In particular, if every $F_i$ is a finite subset of $\mathcal C$, some $t\in\mathcal C$ lies in none of the $F_i$. Moreover $|\iota\times\{0,1\}|<\mathfrak c$.
--   3. **Binary coding.** $|\{0,1\}^{\mathbb N}|=\mathfrak c$, and $\mathrm{bin}:\mathcal C\to\{0,1\}^{\mathbb N}$ denotes a fixed bijection from $\mathcal C$ onto the set of infinite binary sequences.
--
--   The index set $\mathcal C$ is the time axis of the transfinite recursion that builds the bases of the self-dual matroid on $E_0=D\times\{0,1\}$ and the value set of the ordinal rank functions. Item 2 is the counting principle used at single steps of these arguments: when fewer than $\mathfrak c$ finite sets of indices have to be avoided, a suitable index remains. The binary coding attaches a distinct infinite binary string to every index, from which the column sets of the construction are built. The bounds in item 2 only use $\bigl|\bigcup_iF_i\bigr|\le\max(|\iota|,\aleph_0)$ and $\aleph_0<\mathfrak c$; regularity of $\mathfrak c$ is not assumed.
--
--   **Formalization Note** `CIndex` is `Cardinal.continuum.ord.ToType`, a type in `Type` carrying the well-order of the ordinal; $\iota$ and $\alpha$ also live in `Type`. The facts in items 1 to 3 are `cindex_card`, `cindex_initial`, `cindex_predecessors`, `finite_union_small`, `exists_avoid_finite_family`, `cardinal_prod_bool_lt` and `binary_card`; the bijection `cindexBinaryEquiv : CIndex ≃ (ℕ → Bool)` is chosen with `Classical.choice`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Cardinality.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Cardinality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves

namespace OAI

section

open Set Cardinal

namespace InfiniteMatroidCounterexample

abbrev CIndex := Cardinal.continuum.{0}.ord.ToType

lemma cindex_card : Cardinal.mk CIndex = Cardinal.continuum := Cardinal.mk_ord_toType _

lemma cindex_initial : (Cardinal.mk CIndex).ord = Ordinal.type ((· < ·) : CIndex → CIndex → Prop) := by
  rw [cindex_card, Ordinal.type_toType]

lemma cindex_predecessors (i : CIndex) : Cardinal.mk (Iio i) < Cardinal.continuum := by
  simpa only [cindex_card] using Cardinal.mk_Iio_lt i cindex_initial

/-- Cardinal arithmetic used at each stage; it does not assert regularity of the continuum. -/
lemma finite_union_small {α ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (F : ι → Set α) (hF : ∀ i, (F i).Finite) :
    Cardinal.mk (⋃ i, F i) < Cardinal.continuum := by
  calc
    Cardinal.mk (⋃ i, F i) ≤ Cardinal.mk ι * ⨆ i, Cardinal.mk (F i) := Cardinal.mk_iUnion_le F
    _ ≤ max (Cardinal.mk ι) ℵ₀ * max (Cardinal.mk ι) ℵ₀ := by
      apply mul_le_mul' (le_max_left _ _)
      apply ciSup_le'
      intro i
      let := (hF i).fintype
      exact (Cardinal.lt_aleph0_of_finite (F i)).le.trans (le_max_right _ _)
    _ = max (Cardinal.mk ι) ℵ₀ := Cardinal.mul_eq_self (le_max_right _ _)
    _ < Cardinal.continuum := max_lt hι Cardinal.aleph0_lt_continuum

lemma exists_avoid_finite_family {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (F : ι → Set CIndex) (hF : ∀ i, (F i).Finite) :
    ∃ t : CIndex, ∀ i, t ∉ F i := by
  have hcard := finite_union_small hι F hF
  have hn : (⋃ i, F i) ≠ Set.univ := by
    intro heq
    rw [heq, Cardinal.mk_univ, cindex_card] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).mp hn
  exact ⟨t, fun i hi ↦ ht (mem_iUnion.mpr ⟨i, hi⟩)⟩

lemma binary_card : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.mk_fintype, Fintype.card_bool, Cardinal.mk_nat, Cardinal.lift_id, Nat.cast_ofNat]
  exact Cardinal.two_power_aleph0

noncomputable def cindexBinaryEquiv : CIndex ≃ (ℕ → Bool) :=
  Classical.choice (Cardinal.eq.mp (cindex_card.trans binary_card.symm))

lemma cardinal_prod_bool_lt {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum) :
    Cardinal.mk (ι × Bool) < Cardinal.continuum := by
  rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
  have hb : Cardinal.mk Bool ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite Bool).le
  calc
    _ ≤ max (Cardinal.mk ι) ℵ₀ * max (Cardinal.mk ι) ℵ₀ :=
      mul_le_mul' (le_max_left _ _) (hb.trans (le_max_right _ _))
    _ = max (Cardinal.mk ι) ℵ₀ := Cardinal.mul_eq_self (le_max_right _ _)
    _ < Cardinal.continuum := max_lt hι Cardinal.aleph0_lt_continuum
end InfiniteMatroidCounterexample
end

end OAI


