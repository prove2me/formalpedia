-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
-- name    : OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:42:09.592117+00:00
-- url     : https://prove2.me/theorems/944f2a43-0b10-4bd9-b0ca-e52e1ed9dcdf
-- title:
--   Complementary prototype pairs and extending a good prototype family at an unmet pair
-- statement:
--   Notation follows the prototype definitions: $D$ is the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ a Boolean function of $m$ variables, $E_0=D\times\{0,1\}$, complements $X^c$ are taken in $E_0$, *small* means block density tending to $0$, a prototype is a pair $p=(T_p,s_p)$ with $T_p\subseteq E_0$ and $s_p\in\{0,1\}$, $\mathcal B(P)$ is the family of prototype bases of a set $P$ of prototypes, a family $\mathcal F$ *meets* $(I,Y)$ if some $B'\in\mathcal F$ satisfies $B'\subseteq I$, or $I\subseteq B'\subseteq Y$, or $Y\subseteq B'$, and *good* refers to a fixed rank model $R$ on $D$ with ultrafilter $\mathcal U$ and rank function $\rho$. For $X\subseteq E_0$ write $X_0=\{d:(d,0)\in X\}$ and $X_1=\{d:(d,1)\in X\}$. Besides admissible sets, $R$ singles out *upper* sets: $X_0\in\mathcal U$ and either $D\setminus X_1\notin\mathcal U$, or $D\setminus X_1\in\mathcal U$ with $\rho(X_0)\le\rho(D\setminus X_1)$; a set is *lower* if its complement is upper, and the admissible sets are exactly those that are neither upper nor lower.
--
--   1. **Complementary prototype pair.** For $B\subseteq E_0$,
--   $$\pi(B)=\{(B,0),\ (B^c,1)\},$$
--   the lower prototype of $B$ together with its flip. It is a finite set of prototypes.
--
--   The file proves the following facts about adding such pairs.
--
--   - *Union.* If $P$ and $Q$ are good and, for all $p\in P$ and $q\in Q$, neither $T_p\setminus T_q$ nor $T_q\setminus T_p$ is small, then $P\cup Q$ is good.
--   - *Pairs.* Assume the ideal of $R$ is the column ideal $\mathcal K$ of the construction. If $B$ is $R$-admissible then $\pi(B)$ is good. If moreover $P$ is good and, for every $p\in P$, neither $B\setminus T_p$ nor $T_p\setminus B$ is small, then $P\cup\pi(B)$ is good.
--   - *Distance from the zones* (same assumption on the ideal). If $I$ is upper and $T$ is admissible, then $I\setminus T$ is not small; if $Y$ is lower and $T$ is admissible, then $T\setminus Y$ is not small.
--   - *Extension at an unmet pair* (same assumption on the ideal). If $P$ is good, the cardinality of $P$ is strictly smaller than the continuum $2^{\aleph_0}$, $I\subseteq Y\subseteq E_0$, and $\mathcal B(P)$ does not meet $(I,Y)$, then there is $B\subseteq E_0$ such that $P\cup\pi(B)$ is good and $\mathcal B(P\cup\pi(B))$ meets $(I,Y)$.
--
--   This is the single step of the continuum-length recursion that builds the bases of the self-dual matroid: every pair $I\subseteq Y$ that is not yet met is handled by adding one complementary pair of prototypes, while goodness (admissibility, flip closure and separation) is preserved. The cardinality bound is what allows a new admissible set to be chosen that is separated from all earlier prototypes.
--
--   **Formalization Note** `prototypePair B` is the set `{(B,false),(Bᶜ,true)}` of `Prototype = Set E0 × Bool`. The lemmas are `prototypePair_finite`, `mem_prototypePair`, `RankModel.good_union`, `good_pair`, `good_insert_pair`, `upper_difference_positive`, `lower_difference_positive` and `extend_unmet`; all of the `RankModel` lemmas except `good_union` carry the hypothesis `R.ideal = KIdeal`. The cardinality condition is `Cardinal.mk P < Cardinal.continuum`. `symmDiff_inter_right` is the plumbing identity $X\triangle(X\cap Y)=X\setminus Y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/PrototypeExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/PrototypeExtension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

def prototypePair (B : Set E0) : Set Prototype := {(B,false),(Bᶜ,true)}
lemma mem_prototypePair {B : Set E0} {p : Prototype} :
    p ∈ prototypePair B ↔ p = (B,false) ∨ p = (Bᶜ,true) := by
  simp only [prototypePair,Set.mem_insert_iff,Set.mem_singleton_iff]
lemma prototypePair_finite (B : Set E0) : (prototypePair B).Finite := (Set.finite_singleton _).insert _
lemma symmDiff_inter_right (X Y : Set E0) : X ∆ (X ∩ Y) = X \ Y := by
  ext x
  simp only [Set.mem_symmDiff,Set.mem_inter_iff,Set.mem_sdiff]
  tauto

namespace RankModel
variable (R : RankModel D)

lemma good_union {P Q : Set Prototype} (hP : R.GoodPrototypes P) (hQ : R.GoodPrototypes Q)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, ¬ Small (p.1 \ q.1) ∧ ¬ Small (q.1 \ p.1)) :
    R.GoodPrototypes (P ∪ Q) := by
  constructor
  · intro p hp
    exact hp.elim (hP.admissible p) (hQ.admissible p)
  · intro p hp
    exact hp.elim (fun h ↦ Or.inl (hP.flip_closed p h)) (fun h ↦ Or.inr (hQ.flip_closed p h))
  · intro p hp q hq hne
    rcases hp with hp|hp <;> rcases hq with hq|hq
    · exact hP.separated p hp q hq hne
    · exact (hPQ p hp q hq).1
    · exact (hPQ q hq p hp).2
    · exact hQ.separated p hp q hq hne

variable (hK : R.ideal = KIdeal)
include hK
lemma good_pair {B : Set E0} (hB : R.Admissible B) : R.GoodPrototypes (prototypePair B) := by
  constructor
  · intro p hp
    rcases mem_prototypePair.mp hp with rfl|rfl
    · exact hB
    · exact R.admissible_compl hB
  · intro p hp
    rcases mem_prototypePair.mp hp with rfl|rfl
    · exact mem_prototypePair.mpr (Or.inr rfl)
    · exact mem_prototypePair.mpr (Or.inl (by simp [flipPrototype]))
  · intro p hp q hq hne
    rcases mem_prototypePair.mp hp with rfl|rfl <;>
      rcases mem_prototypePair.mp hq with rfl|rfl
    · exact (hne rfl).elim
    · simpa only [Set.sdiff_compl,Set.inter_self] using R.admissible_positive hK hB
    · simpa only [Set.sdiff_eq_compl_inter,Set.inter_self] using
        R.admissible_positive hK (R.admissible_compl hB)
    · exact (hne rfl).elim

lemma good_insert_pair {P : Set Prototype} (hP : R.GoodPrototypes P) {B : Set E0}
    (hB : R.Admissible B)
    (hsep : ∀ p ∈ P, ¬ Small (B \ p.1) ∧ ¬ Small (p.1 \ B)) :
    R.GoodPrototypes (P ∪ prototypePair B) := by
  apply R.good_union hP (R.good_pair hK hB)
  intro p hp q hq
  rcases mem_prototypePair.mp hq with rfl|rfl
  · exact ⟨(hsep p hp).2,(hsep p hp).1⟩
  · have hh := hsep (flipPrototype p) (hP.flip_closed p hp)
    have h1 : p.1 \ Bᶜ = B \ (flipPrototype p).1 := by
      ext x; simp only [flipPrototype,Set.mem_sdiff,Set.mem_compl_iff]; tauto
    have h2 : Bᶜ \ p.1 = (flipPrototype p).1 \ B := by
      ext x; simp only [flipPrototype,Set.mem_sdiff,Set.mem_compl_iff]; tauto
    exact ⟨by rw [h1]; exact hh.1,by rw [h2]; exact hh.2⟩

lemma upper_difference_positive {I T : Set E0} (hI : R.Upper I) (hT : R.Admissible T) :
    ¬ Small (I \ T) := by
  intro hs
  have hi : KSmall0 (I ∆ (I ∩ T)) := by rw [symmDiff_inter_right]; exact small_kSmall0 hs
  have hup : R.Upper (I ∩ T) := ((R.status_invariant hK hi).1).mp hI
  exact ((R.admissible_iff T).mp hT).1 (R.upper_mono hup inter_subset_right)

lemma lower_difference_positive {Y T : Set E0} (hY : R.Lower Y) (hT : R.Admissible T) :
    ¬ Small (T \ Y) := by
  intro hs
  have hi : KSmall0 (T ∆ (T ∩ Y)) := by rw [symmDiff_inter_right]; exact small_kSmall0 hs
  have ht : R.Admissible (T ∩ Y) := ((R.status_invariant hK hi).2.2).mp hT
  exact ((R.admissible_iff _).mp ht).2 (R.lower_mono hY inter_subset_right)

/-- At an unmet interval the exact reservation construction adds one complementary pair. -/
lemma extend_unmet {P : Set Prototype} (hP : R.GoodPrototypes P)
    (hcard : Cardinal.mk P < Cardinal.continuum) {I Y : Set E0} (hIY : I ⊆ Y)
    (hnot : ¬ Meets (PrototypeBases P) I Y) :
    ∃ B, R.GoodPrototypes (P ∪ prototypePair B) ∧ Meets (PrototypeBases (P ∪ prototypePair B)) I Y := by
  have hsep := R.unmet_separation hK hP hIY hnot
  let T : P → Set E0 := fun p ↦ p.1.1
  have hfinish (B : Set E0) (hB : R.Admissible B)
      (hsepB : ∀ p : P, ¬ Small (B \ T p) ∧ ¬ Small (T p \ B))
      (hout : Outcome I Y B) :
      ∃ B, R.GoodPrototypes (P ∪ prototypePair B) ∧ Meets (PrototypeBases (P ∪ prototypePair B)) I Y := by
    refine ⟨B,R.good_insert_pair hK hP hB (fun p hp ↦ hsepB ⟨p,hp⟩),B,?_,hout⟩
    exact ⟨(B,false),Or.inr (mem_prototypePair.mpr (Or.inl rfl)),localRule_self false B⟩
  by_cases hI : R.Upper I
  · obtain ⟨B,_,hBI,hB,hsepB⟩ := R.insert_prototype hK hcard T (empty_subset I)
      R.not_upper_empty (R.upper_not_lower hI)
      (fun p ↦ by simpa using R.admissible_positive hK (hP.admissible p p.2))
      (fun p ↦ R.upper_difference_positive hK hI (hP.admissible p p.2))
    exact hfinish B hB hsepB (Or.inl hBI)
  by_cases hY : R.Lower Y
  · obtain ⟨B,hYB,_,hB,hsepB⟩ := R.insert_prototype hK hcard T (subset_univ Y)
      (fun h ↦ R.upper_not_lower h hY) R.not_lower_univ
      (fun p ↦ R.lower_difference_positive hK hY (hP.admissible p p.2))
      (fun p ↦ by simpa only [← Set.compl_eq_univ_sdiff] using
        R.admissible_positive hK (R.admissible_compl (hP.admissible p p.2)))
    exact hfinish B hB hsepB (Or.inr (Or.inr hYB))
  obtain ⟨B,hIB,hBY,hB,hsepB⟩ := R.insert_prototype hK hcard T hIY hI hY
    (fun p ↦ (hsep p p.2).1) (fun p ↦ (hsep p p.2).2)
  exact hfinish B hB hsepB (Or.inr (Or.inl ⟨hIB,hBY⟩))

end RankModel
end InfiniteMatroidCounterexample
end

end OAI


