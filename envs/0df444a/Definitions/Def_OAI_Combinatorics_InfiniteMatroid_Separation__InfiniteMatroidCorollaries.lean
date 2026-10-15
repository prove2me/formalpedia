-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Separation__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:50:44.557404+00:00
-- url     : https://prove2.me/theorems/b49bc672-d693-42c6-896c-bc2baaf6a4fc
-- title:
--   Inserting an admissible set separated from fewer than continuum many given sets
-- statement:
--   Notation follows the zone and reservation definitions. $D$ is the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, and $E_0=D\times\{0,1\}$. A set $X\subseteq E_0$ is *small* if its density $|X\cap W_m|/|W_m|$ in the $m$-th block $W_m=\{((m,g),b)\}$ tends to $0$ as $m\to\infty$. Let $R$ be a rank model on $D$, with ultrafilter $\mathcal U$ and rank $\rho$ taking values in the well-ordered continuum index set, and assume that its ideal is the column ideal $\mathcal K$ of the construction. For $X\subseteq E_0$ write $X_b=\{d\in D:(d,b)\in X\}$, with complements of subsets of $D$ taken in $D$. Recall that $X$ is *$R$-admissible* if
--   $$\bigl(X_0\in\mathcal U,\ X_1^c\in\mathcal U,\ \rho(X_1^c)<\rho(X_0)\bigr)\quad\text{or}\quad\bigl(X_0\notin\mathcal U,\ X_1^c\notin\mathcal U,\ \rho(X_1)<\rho(X_0^c)\bigr),$$
--   that $X$ is *upper* if $X_0\in\mathcal U$ and either $X_1^c\notin\mathcal U$, or $X_1^c\in\mathcal U$ and $\rho(X_0)\le\rho(X_1^c)$, and that $X$ is *lower* if $E_0\setminus X$ is upper.
--
--   **Inserting a separated admissible set.** Let $\iota$ be an index set of cardinality strictly less than the continuum, $|\iota|<2^{\aleph_0}$, and let $(T_i)_{i\in\iota}$ be a family of subsets of $E_0$. Let $A\subseteq Z\subseteq E_0$, where $A$ is not upper and $Z$ is not lower, and assume that for every $i\in\iota$ neither $T_i\setminus A$ nor $Z\setminus T_i$ is small. Then there is an $R$-admissible set $B\subseteq E_0$ such that
--   $$A\subseteq B\subseteq Z\qquad\text{and, for every } i\in\iota,\quad B\setminus T_i\ \text{ and }\ T_i\setminus B\ \text{ are not small}.$$
--
--   In the continuum-length construction of the self-dual matroid on $E_0$, the sets $T_i$ are the sets of the fewer than continuum many prototypes chosen so far. A good family of prototypes requires $T_p\setminus T_q$ to be non-small for distinct prototypes $p,q$, so this result produces a new admissible prototype set inside a prescribed interval $[A,Z]$ that is separated, in both directions, from every earlier one. Without the separation conclusion the statement is just the existence of an admissible set between a non-upper and a non-lower set; the content here is that separation from fewer than continuum many sets can be achieved at the same time.
--
--   **Formalization Note** The statement is `RankModel.insert_prototype` for `R : RankModel D` with the hypothesis `hK : R.ideal = KIdeal`. The index set is `ι : Type` with `Cardinal.mk ι < Cardinal.continuum`, the family is `T : ι → Set E0`, and the zone hypotheses are `¬ R.Upper A` and `¬ R.Lower Z`. The file also contains a private copy of the core lemma `ite_eq_left` (an `if` whose condition holds evaluates to its first branch), which is plumbing for the Lean version.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Separation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Separation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones__InfiniteMatroidCorollaries

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample
namespace RankModel

variable (R : RankModel D) (hK : R.ideal = KIdeal)
include hK

lemma insert_prototype {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (T : ι → Set E0) {A Z : Set E0} (hAZ : A ⊆ Z)
    (hA : ¬ R.Upper A) (hZ : ¬ R.Lower Z)
    (hTA : ∀ i, ¬ Small (T i \ A)) (hZT : ∀ i, ¬ Small (Z \ T i)) :
    ∃ B, A ⊆ B ∧ B ⊆ Z ∧ R.Admissible B ∧
      ∀ i, ¬ Small (B \ T i) ∧ ¬ Small (T i \ B) := by
  classical
  let G := Z \ A
  let S0 (i : ι) : Set E0 := if Small (A \ T i) then G \ T i else Z \ T i
  let S1 (i : ι) : Set E0 := if Small (T i \ Z) then T i ∩ G else T i \ A
  have h0 (i : ι) : ¬ Small (S0 i) := by
    dsimp only [S0]
    split_ifs with hs
    · intro hg
      apply hZT i
      apply small_subset (small_union hs hg)
      intro x hx
      change x ∈ (A \ T i) ∪ ((Z \ A) \ T i)
      simp only [Set.mem_union,Set.mem_sdiff] at hx ⊢
      tauto
    · exact hZT i
  have h1 (i : ι) : ¬ Small (S1 i) := by
    dsimp only [S1]
    split_ifs with hs
    · intro hg
      apply hTA i
      apply small_subset (small_union hs hg)
      intro x hx
      change x ∈ (T i \ Z) ∪ (T i ∩ (Z \ A))
      simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff] at hx ⊢
      tauto
    · exact hTA i
  let traces (p : ι × Bool) : Set E0 := if p.2 then S1 p.1 else S0 p.1
  have ht : ∀ p, ¬ Small (traces p) := by
    rintro ⟨i,b⟩; cases b
    · exact h0 i
    · exact h1 i
  obtain ⟨t,hres⟩ := simultaneous_reservations (cardinal_prod_bool_lt hι) traces ht
  have hr0 (i : ι) : ¬ Small (S0 i ∩ HCell t false) := hres (i,false) false
  have hr1 (i : ι) : ¬ Small (S1 i ∩ HCell t true) := hres (i,true) true
  let A' := A ∪ (HCell t false ∩ G)
  let Z' := Z \ (HCell t true ∩ G)
  have hAA : A ⊆ A' := Set.subset_union_left
  have hZZ : Z' ⊆ Z := Set.sdiff_subset
  have hAZ' : A' ⊆ Z' := by
    intro x hx
    refine ⟨?_,?_⟩
    · rcases hx with hx | hx
      · exact hAZ hx
      · exact hx.2.1
    · intro hh
      rcases hx with hx | hx
      · exact hh.2.2 hx
      · exact Set.disjoint_left.mp (hCell_disjoint t) hx.1 hh.1
  have haInv : KSmall0 (A ∆ A') := by
    apply kSmall0_mono (hCell_kSmall0 t false)
    intro x hx
    change x ∈ A ∆ (A ∪ (HCell t false ∩ G)) at hx
    simp only [Set.mem_symmDiff,Set.mem_union,Set.mem_inter_iff] at hx
    tauto
  have hzInv : KSmall0 (Z ∆ Z') := by
    apply kSmall0_mono (hCell_kSmall0 t true)
    intro x hx
    change x ∈ Z ∆ (Z \ (HCell t true ∩ G)) at hx
    simp only [Set.mem_symmDiff,Set.mem_sdiff,Set.mem_inter_iff] at hx
    tauto
  have haU : ¬ R.Upper A' := ((R.status_invariant hK haInv).1).not.mp hA
  have hzL : ¬ R.Lower Z' := ((R.status_invariant hK hzInv).2.1).not.mp hZ
  obtain ⟨B,hAB,hBZ,hB⟩ := R.exists_admissible_between hAZ' haU hzL
  refine ⟨B,hAA.trans hAB,hBZ.trans hZZ,hB,fun i ↦ ⟨?_,?_⟩⟩
  · by_cases hs : Small (A \ T i)
    · have hr : ¬ Small ((G \ T i) ∩ HCell t false) := by simpa only [S0,ite_eq_left hs] using hr0 i
      intro hbad
      apply hr
      apply small_subset hbad
      intro x hx
      exact ⟨hAB (Or.inr ⟨hx.2,hx.1.1⟩),hx.1.2⟩
    · exact fun hb ↦ hs (small_subset hb (Set.sdiff_subset_sdiff_left (hAA.trans hAB)))
  · by_cases hs : Small (T i \ Z)
    · have hr : ¬ Small ((T i ∩ G) ∩ HCell t true) := by simpa only [S1,ite_eq_left hs] using hr1 i
      intro hbad
      apply hr
      apply small_subset hbad
      intro x hx
      exact ⟨hx.1.1,fun hxB ↦ (hBZ hxB).2 ⟨hx.2,hx.1.2⟩⟩
    · exact fun hb ↦ hs (small_subset hb (Set.sdiff_subset_sdiff_right (hBZ.trans hZZ)))

end RankModel
end InfiniteMatroidCounterexample
end

end OAI


