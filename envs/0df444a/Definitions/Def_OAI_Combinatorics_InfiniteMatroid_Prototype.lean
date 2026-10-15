-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
-- name    : OAI_Combinatorics_InfiniteMatroid_Prototype
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:11:10.204429+00:00
-- url     : https://prove2.me/theorems/f1d1e2ca-f69a-464a-8ebc-0b7ad9061abd
-- title:
--   Interval outcomes, prototypes and prototype bases
-- statement:
--   This file sets up the bookkeeping for assembling a family of bases out of *prototypes*. Throughout, $D$ is the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ a Boolean function of $m$ variables, and $E_0=D\times\{0,1\}$; complements $X^c$ are taken in $E_0$. A set $X\subseteq E_0$ is *small* if its density in the $m$-th block $W_m=\{((m,g),b)\}$ tends to $0$ as $m\to\infty$, and $X$ lies in the *class* of $T$ if $X\triangle T$ is small. For $T\subseteq E_0$ and a bit $s\in\{0,1\}$, $\mathcal L_s(T)$ denotes the local basis rule: $\mathcal L_0(T)$ consists of the sets $X$ in the class of $T$ whose probe lower limit $\liminf_n \phi^T_n(X)$ lies in $(-1,0]$, and $\mathcal L_1(T)=\{X : X^c\in\mathcal L_0(T^c)\}$.
--
--   1. **Interval outcomes.** For $I,Y,B\subseteq E_0$, the set $B$ is an *outcome* for the pair $(I,Y)$ if
--   $$B\subseteq I\quad\text{or}\quad I\subseteq B\subseteq Y\quad\text{or}\quad Y\subseteq B .$$
--   Complementation reverses the pair: if $B$ is an outcome for $(I,Y)$, then $B^c$ is an outcome for $(Y^c,I^c)$.
--   2. **Meeting a pair.** A family $\mathcal F$ of subsets of $E_0$ *meets* $(I,Y)$ if some member of $\mathcal F$ is an outcome for $(I,Y)$; if $\mathcal F\subseteq\mathcal G$ and $\mathcal F$ meets $(I,Y)$, so does $\mathcal G$.
--   3. **Prototypes and flips.** A prototype is a pair $p=(T_p,s_p)$ with $T_p\subseteq E_0$ and $s_p\in\{0,1\}$ (the bit selects the lower rule $\mathcal L_0$ or the upper rule $\mathcal L_1$). Its flip is $\bar p=(T_p^c,\,1-s_p)$, and flipping twice returns $p$.
--   4. **Prototype bases.** For a set $P$ of prototypes,
--   $$\mathcal B(P)=\bigcup_{p\in P}\mathcal L_{s_p}(T_p),$$
--   so $\mathcal L_{s_p}(T_p)\subseteq\mathcal B(P)$ for every $p\in P$.
--   5. **Good prototype families.** Fix a rank model $R$ on $D$ (a proper ideal and an ultrafilter on $D$ avoiding it, together with a rank function on subsets of $D$ taking values in the well-ordered continuum index set). A set $P$ of prototypes is *good* if (a) $T_p$ is $R$-admissible for every $p\in P$ (admissibility is the rank condition on the two slices $\{d:(d,0)\in T_p\}$ and $\{d:(d,1)\in T_p\}$), (b) $P$ is closed under flips, and (c) $T_p\setminus T_q$ is not small whenever $p\ne q$ both lie in $P$.
--
--   The file also records the facts linking these notions. If $I$ lies in the class of $T$, $I\subseteq Y$ and $Y\setminus I$ is small, then $Y$ lies in the class of $T$. If neither $T$ nor $T^c$ is small and $I\subseteq Y$, then for each $s\in\{0,1\}$ the rule $\mathcal L_s(T)$ meets $(I,Y)$ as soon as $T\setminus I$ is small, and also as soon as $Y\setminus T$ is small. Consequently (*unmet separation*): if the ideal of $R$ is the column ideal $\mathcal K$ of the construction, $P$ is good, $I\subseteq Y$ and $\mathcal B(P)$ does not meet $(I,Y)$, then for every $p\in P$ neither $T_p\setminus I$ nor $Y\setminus T_p$ is small.
--
--   These objects are the raw material of the self-dual matroid on $E_0$: its bases are the prototype bases $\mathcal B(P)$ of a good family $P$ that meets every pair $I\subseteq Y$, and meeting every such pair in particular gives the interval alternative used to verify the matroid maximality axiom. Unmet separation says that a pair not yet met is far from every existing prototype, which is what leaves room to insert a new one.
--
--   **Formalization Note** `Prototype` is `Set E0 × Bool` (`false` is the lower rule, `true` the upper rule). The definitions are `Outcome`, `Meets`, `flipPrototype`, `PrototypeBases` and the structure `RankModel.GoodPrototypes` with fields `admissible`, `flip_closed`, `separated`. The accompanying lemmas are `sameClass_of_small_gap`, `outcome_compl`, `meets_mono`, `localRule_meets_of_small_left`, `localRule_meets_of_small_right`, `localRule_subset_bases`, the simp lemma `flipPrototype_flip`, and `RankModel.unmet_separation`, which assumes `R.ideal = KIdeal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Prototype.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Prototype.lean by skeleton subtraction
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

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma sameClass_of_small_gap {T I Y : Set E0} (hI : SameClass T I) (hIY : I ⊆ Y)
    (hgap : Small (Y \ I)) : SameClass T Y := by
  apply sameClass_trans hI
  apply small_subset hgap
  intro x hx
  rcases hx with hx|hx
  · exact hx
  · exact (hx.2 (hIY hx.1)).elim

def Outcome (I Y B : Set E0) : Prop := B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B
lemma outcome_compl {I Y B : Set E0} (h : Outcome I Y B) : Outcome Yᶜ Iᶜ Bᶜ := by
  rcases h with h | ⟨h1,h2⟩ | h
  · exact Or.inr (Or.inr (compl_subset_compl.mpr h))
  · exact Or.inr (Or.inl ⟨compl_subset_compl.mpr h2,compl_subset_compl.mpr h1⟩)
  · exact Or.inl (compl_subset_compl.mpr h)

def Meets (F : Set (Set E0)) (I Y : Set E0) : Prop := ∃ B ∈ F, Outcome I Y B
lemma meets_mono {F G : Set (Set E0)} (hFG : F ⊆ G) {I Y : Set E0} (h : Meets F I Y) : Meets G I Y := by
  obtain ⟨B,hB,hout⟩ := h
  exact ⟨B,hFG hB,hout⟩

lemma localRule_meets_of_small_left (s : Bool) {T I Y : Set E0}
    (hT : ¬ Small T) (hTc : ¬ Small Tᶜ) (hIY : I ⊆ Y) (hTI : Small (T \ I)) :
    Meets (LocalRule s T) I Y := by
  by_cases hI : SameClass T I
  · by_cases hg : Small (Y \ I)
    · exact localRule_interval s hT hTc hIY hI (sameClass_of_small_gap hI hIY hg)
    · obtain ⟨B,hB,hBI | hIBY⟩ := localRule_lower_endpoint s hT hTc hIY hI hg
      · exact ⟨B,hB,Or.inl hBI⟩
      · exact ⟨B,hB,Or.inr (Or.inl hIBY)⟩
  · have hj : SameClass T (T ∩ I) := by
      apply small_subset hTI
      intro x hx
      simp only [Set.mem_symmDiff,Set.mem_inter_iff,Set.mem_sdiff] at hx ⊢
      tauto
    have hg : ¬ Small (I \ (T ∩ I)) := by
      intro h
      apply hI
      apply small_subset (small_union h hTI)
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl ⟨hx.1,fun hi ↦ hx.2 hi.1⟩
      · exact Or.inr hx
    obtain ⟨B,hB,hBJ | ⟨_,hBI⟩⟩ := localRule_lower_endpoint s hT hTc inter_subset_right hj hg
    · exact ⟨B,hB,Or.inl (hBJ.trans inter_subset_right)⟩
    · exact ⟨B,hB,Or.inl hBI⟩

lemma localRule_meets_of_small_right (s : Bool) {T I Y : Set E0}
    (hT : ¬ Small T) (hTc : ¬ Small Tᶜ) (hIY : I ⊆ Y) (hYT : Small (Y \ T)) :
    Meets (LocalRule s T) I Y := by
  have he : Tᶜ \ Yᶜ = Y \ T := by ext x; simp only [Set.mem_sdiff,Set.mem_compl_iff]; tauto
  obtain ⟨B,hB,hout⟩ := localRule_meets_of_small_left (!s) hTc (by simpa using hT)
    (compl_subset_compl.mpr hIY) (by rwa [he])
  refine ⟨Bᶜ,?_,?_⟩
  · simpa only [Bool.not_not,compl_compl] using localRule_compl hB
  · simpa only [compl_compl] using outcome_compl hout

abbrev Prototype := Set E0 × Bool

def flipPrototype (p : Prototype) : Prototype := (p.1ᶜ,!p.2)
@[simp] lemma flipPrototype_flip (p : Prototype) : flipPrototype (flipPrototype p) = p := by
  simp [flipPrototype]

def PrototypeBases (P : Set Prototype) : Set (Set E0) := {B | ∃ p ∈ P, B ∈ LocalRule p.2 p.1}
lemma localRule_subset_bases {P : Set Prototype} {p : Prototype} (hp : p ∈ P) :
    LocalRule p.2 p.1 ⊆ PrototypeBases P := fun _ h ↦ ⟨p,hp,h⟩

namespace RankModel
variable (R : RankModel D)

structure GoodPrototypes (P : Set Prototype) : Prop where
  admissible : ∀ p ∈ P, R.Admissible p.1
  flip_closed : ∀ p ∈ P, flipPrototype p ∈ P
  separated : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ¬ Small (p.1 \ q.1)

variable (hK : R.ideal = KIdeal)
include hK
lemma unmet_separation {P : Set Prototype} (hP : R.GoodPrototypes P)
    {I Y : Set E0} (hIY : I ⊆ Y) (hnot : ¬ Meets (PrototypeBases P) I Y) :
    ∀ p ∈ P, ¬ Small (p.1 \ I) ∧ ¬ Small (Y \ p.1) := by
  intro p hp
  have ht := R.admissible_positive hK (hP.admissible p hp)
  have htc := R.admissible_positive hK (R.admissible_compl (hP.admissible p hp))
  exact ⟨fun hs ↦ hnot (meets_mono (localRule_subset_bases hp)
    (localRule_meets_of_small_left p.2 ht htc hIY hs)),
    fun hs ↦ hnot (meets_mono (localRule_subset_bases hp)
    (localRule_meets_of_small_right p.2 ht htc hIY hs))⟩

end RankModel
end InfiniteMatroidCounterexample
end

end OAI


