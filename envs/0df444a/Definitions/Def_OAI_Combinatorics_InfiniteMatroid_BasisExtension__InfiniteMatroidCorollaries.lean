-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_BasisExtension__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:46:03.912905+00:00
-- url     : https://prove2.me/theorems/a2bc8492-7a52-4358-9cca-3671fa953fbc
-- title:
--   Upper and lower local basis rules: complementation, class bookkeeping and interval alternatives
-- statement:
--   Notation follows the block-density and local-basis definitions. $D$ is the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ a Boolean function of $m$ variables, $E_0=D\times\{0,1\}$, and complements $X^c$ are taken in $E_0$. The $m$-th block $W_m\subseteq E_0$ consists of the $2\cdot2^{2^m}$ elements $((m,g),b)$, $P_n=W_0\cup\dots\cup W_{n-1}$, and $\delta_m(X)=|X\cap W_m|/|W_m|$. A set $X\subseteq E_0$ is *small* if $\delta_m(X)\to0$ as $m\to\infty$, and $X$ lies in the *class* of $T$ if the symmetric difference $X\triangle T$ is small. For $T,X\subseteq E_0$ and $n\in\mathbb N$ the probe is
--
--   $$\phi^T_n(X)=\bigl(|X\cap P_n|-|T\cap P_n|\bigr)+|P_n|\Bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\Bigr),\qquad d^T_m(X)=\delta_m(X)-\delta_m(T),$$
--
--   $\underline\phi^{\,T}(X)=\liminf_{n\to\infty}\phi^T_n(X)\in[-\infty,+\infty]$ is its lower limit, and the lower local rule of $T$ is
--   $\mathcal L_0(T)=\{X\subseteq E_0:\ X\text{ lies in the class of }T\text{ and }-1<\underline\phi^{\,T}(X)\le0\}$.
--
--   1. **Upper local rule.** For $T\subseteq E_0$,
--   $$\mathcal L_1(T)=\{X\subseteq E_0:\ X^c\in\mathcal L_0(T^c)\}.$$
--   2. **Local rule selected by a bit.** For $s\in\{0,1\}$ and $T\subseteq E_0$, $\mathcal L_s(T)$ is $\mathcal L_0(T)$ if $s=0$ and $\mathcal L_1(T)$ if $s=1$.
--
--   The file proves the following facts, in which $T,X,G,P,I,Y$ are arbitrary subsets of $E_0$ unless further conditions are stated.
--
--   - *Class bookkeeping.* If $X$ lies in the class of $T$, then $X^c$ lies in the class of $T^c$; for every small $P$ both $X\cup P$ and $X\setminus P$ lie in the class of $T$; and if moreover $T$ is not small, then $X$ is not small.
--   - *Deleting inside a pool.* If $X$ lies in the class of $T$ and $G\subseteq X$ is not small, then there is a small set $P\subseteq G$ with $\phi^T_n(X\setminus P)\to-\infty$ as $n\to\infty$.
--   - *Reflexivity and complementation.* $T\in\mathcal L_s(T)$ for both values of $s$, and $X\in\mathcal L_s(T)$ implies $X^c\in\mathcal L_{1-s}(T^c)$.
--   - *Upward correction.* If $X$ lies in the class of $T$, $\underline\phi^{\,T}(X)\le-1$, and $G\subseteq X^c$ is not small, then some $B\in\mathcal L_0(T)$ satisfies $X\subseteq B\subseteq X\cup G$.
--   - *Downward correction.* If $X$ lies in the class of $T$, $\underline\phi^{\,T}(X)>0$, and $G\subseteq X$ is not small, then some $B\in\mathcal L_0(T)$ satisfies $X\setminus G\subseteq B\subseteq X$.
--   - *Interval alternative.* If neither $T$ nor $T^c$ is small, $I\subseteq Y$, and both $I$ and $Y$ lie in the class of $T$, then for each $s\in\{0,1\}$ there is $B\in\mathcal L_s(T)$ with
--   $$B\subseteq I\quad\text{or}\quad I\subseteq B\subseteq Y\quad\text{or}\quad Y\subseteq B .$$
--   - *Lower endpoint in the class.* If $T$ is not small, $I\subseteq Y$, $I$ lies in the class of $T$ and $Y\setminus I$ is not small, then there is $B\in\mathcal L_0(T)$ with $B\subseteq I$ or $I\subseteq B\subseteq Y$. The same conclusion, with $\mathcal L_s(T)$ in place of $\mathcal L_0(T)$, holds for each $s\in\{0,1\}$ under the additional hypothesis that $T^c$ is not small.
--   - *Upper endpoint in the class.* If $T^c$ is not small, $I\subseteq Y$, $Y$ lies in the class of $T$ and $Y\setminus I$ is not small, then there is $B\in\mathcal L_0(T)$ with $I\subseteq B\subseteq Y$ or $Y\subseteq B$.
--
--   The local rules $\mathcal L_s(T)$ are the pieces from which the bases of the self-dual matroid on $E_0$ are assembled, one piece for each prototype $(T,s)$; the upper rule is defined so that complementation exchanges the two rules together with $T$ and $T^c$. The interval statements say that a single local rule already meets an interval $[I,Y]$ (contains some $B\subseteq I$, or some $B$ with $I\subseteq B\subseteq Y$, or some $B\supseteq Y$) once both endpoints, or one endpoint together with a non-small gap $Y\setminus I$, lie in the class of $T$, under the stated non-smallness assumptions on $T$ and $T^c$. The correction statements move a set of the class into $\mathcal L_0(T)$ by adding part of a non-small pool outside it, or by removing part of a non-small pool inside it.
--
--   **Formalization Note** `LocalUpper T` is `{X | Xᶜ ∈ LocalLower Tᶜ}`, and `LocalRule s T` is `LocalUpper T` for `s = true` and `LocalLower T` for `s = false`; the flipped bit in `localRule_compl` is `!s`. Lower limits are `probeLiminf (fProbe T) X`, valued in `EReal`, so the hypotheses $\underline\phi^{\,T}(X)\le-1$ and $\underline\phi^{\,T}(X)>0$ include the values $-\infty$ and $+\infty$ respectively; divergence to $-\infty$ is `Tendsto (fun n ↦ fProbe T n (X \ P)) atTop atBot`. The lemmas are `sameClass_compl`, `sameClass_add`, `sameClass_delete`, `positive_sameClass`, `positive_pool_delete`, `localLower_self`, `localRule_self`, `localRule_compl`, `localLower_correct_up`, `localLower_correct_down`, `localLower_interval`, `localRule_interval`, `localLower_lower_endpoint`, `localRule_lower_endpoint` and `localLower_upper_endpoint`. The hypothesis `¬ Small Tᶜ` of `localRule_lower_endpoint` is part of its statement for both values of `s`, although it is not used in its proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/BasisExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/BasisExtension.lean by skeleton subtraction
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

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma sameClass_compl {T X : Set E0} (h : SameClass T X) : SameClass Tᶜ Xᶜ := by
  have he : Xᶜ ∆ Tᶜ = X ∆ T := by ext x; simp only [mem_symmDiff, mem_compl_iff]; tauto
  simpa only [SameClass, he] using h

lemma sameClass_add {T X P : Set E0} (h : SameClass T X) (hP : Small P) : SameClass T (X ∪ P) := by
  apply sameClass_trans h
  apply small_subset hP
  intro x hx
  simp only [mem_symmDiff, Set.mem_union] at hx
  tauto

lemma sameClass_delete {T X P : Set E0} (h : SameClass T X) (hP : Small P) : SameClass T (X \ P) := by
  apply sameClass_trans h
  apply small_subset hP
  intro x hx
  simp only [mem_symmDiff, Set.mem_sdiff] at hx
  tauto

lemma positive_sameClass {T X : Set E0} (hT : ¬ Small T) (h : SameClass T X) : ¬ Small X := by
  intro hX
  apply hT
  apply small_subset (small_union hX h)
  intro x hx
  simp only [Set.mem_union, mem_symmDiff]
  tauto

lemma positive_pool_delete {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ X) :
    ∃ P, P ⊆ G ∧ Small P ∧ Tendsto (fun n ↦ fProbe T n (X \ P)) atTop atBot := by
  obtain ⟨P,hPG,hP,ht⟩ := positive_pool_add (sameClass_compl hX) hG (by simpa using hGX)
  refine ⟨P,hPG,hP,?_⟩
  have he (n : ℕ) : fProbe T n (X \ P) = -fProbe Tᶜ n (Xᶜ ∪ P) := by
    have hc : (X \ P)ᶜ = Xᶜ ∪ P := by ext x; simp only [mem_compl_iff, Set.mem_sdiff, Set.mem_union]; tauto
    rw [← hc, fProbe_compl, neg_neg]
  simpa only [he, Function.comp_def] using (tendsto_neg_atTop_atBot.comp ht)

lemma localLower_self (T : Set E0) : T ∈ LocalLower T := by
  refine ⟨sameClass_refl _,?_⟩
  have hz (n : ℕ) : fProbe T n T = 0 := by
    have hd : dProbe T T = fun _ ↦ 0 := funext fun _ ↦ sub_self _
    have ht (n : ℕ) : tailSup (fun _ ↦ (0:ℝ)) n = 0 ∧ tailInf (fun _ ↦ (0:ℝ)) n = 0 := by
      simp [tailSup, tailInf, (nonempty_Ici (a := n)).image_const]
    simp [fProbe, pProbe, hd, (ht n).1, (ht n).2]
  simp [LowerBasis, probeLiminf, hz]

lemma localLower_correct_up {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ Xᶜ) (hlo : probeLiminf (fProbe T) X ≤ -1) :
    ∃ B ∈ LocalLower T, X ⊆ B ∧ B ⊆ X ∪ G := by
  obtain ⟨P,hPG,hP,ht⟩ := positive_pool_add hX hG hGX
  have hlim : probeLiminf (fProbe T) (X ∪ P) = ⊤ := (EReal.tendsto_coe_atTop.comp ht).liminf_eq
  obtain ⟨B,hXB,hBP,hBT,hB⟩ := fProbe_interpolation hX (sameClass_add hX hP)
    (Set.subset_union_left) hlo (by rw [hlim]; exact EReal.coe_lt_top 0)
  exact ⟨B,⟨hBT,hB⟩,hXB,hBP.trans (union_subset_union_right X hPG)⟩

lemma localLower_correct_down {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ X) (hhi : 0 < probeLiminf (fProbe T) X) :
    ∃ B ∈ LocalLower T, X \ G ⊆ B ∧ B ⊆ X := by
  obtain ⟨P,hPG,hP,ht⟩ := positive_pool_delete hX hG hGX
  have hlim : probeLiminf (fProbe T) (X \ P) = ⊥ := (EReal.tendsto_coe_atBot.comp ht).liminf_eq
  obtain ⟨B,hPB,hBX,hBT,hB⟩ := fProbe_interpolation (sameClass_delete hX hP) hX
    sdiff_subset (by rw [hlim]; exact bot_le) hhi
  exact ⟨B,⟨hBT,hB⟩,(Set.sdiff_subset_sdiff_right hPG).trans hPB,hBX⟩

/-- Upper rule with its complement identity built into the definition. -/
def LocalUpper (T : Set E0) : Set (Set E0) := {X | Xᶜ ∈ LocalLower Tᶜ}

def LocalRule (upper : Bool) (T : Set E0) : Set (Set E0) :=
  if upper then LocalUpper T else LocalLower T

lemma localRule_self (s : Bool) (T : Set E0) : T ∈ LocalRule s T := by
  cases s with
  | false => exact localLower_self _
  | true =>
    change Tᶜ ∈ LocalLower Tᶜ
    exact localLower_self Tᶜ

lemma localRule_compl {s : Bool} {T X : Set E0} (h : X ∈ LocalRule s T) :
    Xᶜ ∈ LocalRule (!s) Tᶜ := by
  cases s with
  | false => simpa [LocalRule,LocalUpper] using h
  | true => exact h

lemma localLower_interval {T I Y : Set E0} (hT : ¬ Small T) (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hY : SameClass T Y) :
    ∃ B ∈ LocalLower T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  by_cases hlo : -1 < probeLiminf (fProbe T) I
  · by_cases hhi : probeLiminf (fProbe T) I ≤ 0
    · exact ⟨I,⟨hI,hlo,hhi⟩,Or.inl Subset.rfl⟩
    · obtain ⟨B,hB,_,hBI⟩ := localLower_correct_down hI (positive_sameClass hT hI)
        Subset.rfl (lt_of_not_ge hhi)
      exact ⟨B,hB,Or.inl hBI⟩
  · by_cases hhi : 0 < probeLiminf (fProbe T) Y
    · obtain ⟨B,hIB,hBY,hBT,hB⟩ := fProbe_interpolation hI hY hIY (le_of_not_gt hlo) hhi
      exact ⟨B,⟨hBT,hB⟩,Or.inr (Or.inl ⟨hIB,hBY⟩)⟩
    · by_cases hyl : -1 < probeLiminf (fProbe T) Y
      · exact ⟨Y,⟨hY,hyl,le_of_not_gt hhi⟩,Or.inr (Or.inr Subset.rfl)⟩
      · obtain ⟨B,hB,hYB,_⟩ := localLower_correct_up hY
          (positive_sameClass hTc (sameClass_compl hY)) Subset.rfl (le_of_not_gt hyl)
        exact ⟨B,hB,Or.inr (Or.inr hYB)⟩

lemma localLower_lower_endpoint {T I Y : Set E0} (hT : ¬ Small T)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalLower T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) := by
  by_cases hlo : -1 < probeLiminf (fProbe T) I
  · by_cases hhi : probeLiminf (fProbe T) I ≤ 0
    · exact ⟨I,⟨hI,hlo,hhi⟩,Or.inl Subset.rfl⟩
    · obtain ⟨B,hB,_,hBI⟩ := localLower_correct_down hI (positive_sameClass hT hI)
        Subset.rfl (lt_of_not_ge hhi)
      exact ⟨B,hB,Or.inl hBI⟩
  · obtain ⟨B,hB,hIB,hBY⟩ := localLower_correct_up hI hgap (fun _ hx ↦ hx.2) (le_of_not_gt hlo)
    exact ⟨B,hB,Or.inr ⟨hIB,hBY.trans (union_subset hIY sdiff_subset)⟩⟩

lemma localLower_upper_endpoint {T I Y : Set E0} (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hY : SameClass T Y) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalLower T, (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  by_cases hhi : 0 < probeLiminf (fProbe T) Y
  · obtain ⟨B,hB,hIB,hBY⟩ := localLower_correct_down hY hgap sdiff_subset hhi
    exact ⟨B,hB,Or.inl ⟨(by intro x hx; exact hIB ⟨hIY hx,fun h ↦ h.2 hx⟩),hBY⟩⟩
  · by_cases hlo : -1 < probeLiminf (fProbe T) Y
    · exact ⟨Y,⟨hY,hlo,le_of_not_gt hhi⟩,Or.inr Subset.rfl⟩
    · obtain ⟨B,hB,hYB,_⟩ := localLower_correct_up hY
        (positive_sameClass hTc (sameClass_compl hY)) Subset.rfl (le_of_not_gt hlo)
      exact ⟨B,hB,Or.inr hYB⟩

lemma localRule_interval (s : Bool) {T I Y : Set E0} (hT : ¬ Small T) (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hY : SameClass T Y) :
    ∃ B ∈ LocalRule s T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  cases s with
  | false => exact localLower_interval hT hTc hIY hI hY
  | true =>
    obtain ⟨B,hB,hBI | ⟨hIB,hBY⟩ | hYB⟩ := localLower_interval hTc (by simpa using hT)
      (compl_subset_compl.mpr hIY) (sameClass_compl hY) (sameClass_compl hI)
    · refine ⟨Bᶜ,?_,Or.inr (Or.inr ?_)⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBI
    · refine ⟨Bᶜ,?_,Or.inr (Or.inl ⟨?_,?_⟩)⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBY
      · simpa using compl_subset_compl.mpr hIB
    · refine ⟨Bᶜ,?_,Or.inl ?_⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hYB

lemma localRule_lower_endpoint (s : Bool) {T I Y : Set E0} (hT : ¬ Small T) (_hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalRule s T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) := by
  cases s with
  | false => exact localLower_lower_endpoint hT hIY hI hgap
  | true =>
    have hg : ¬ Small (Iᶜ \ Yᶜ) := by
      have he : Iᶜ \ Yᶜ = Y \ I := by ext x; simp only [Set.mem_sdiff,mem_compl_iff]; tauto
      rwa [he]
    obtain ⟨B,hB,⟨hIB,hBY⟩ | hYB⟩ := localLower_upper_endpoint (T := Tᶜ) (I := Yᶜ) (Y := Iᶜ)
      (by simpa only [compl_compl] using hT)
      (compl_subset_compl.mpr hIY) (sameClass_compl hI) hg
    · refine ⟨Bᶜ,?_,Or.inr ⟨?_,?_⟩⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBY
      · simpa using compl_subset_compl.mpr hIB
    · refine ⟨Bᶜ,?_,Or.inl ?_⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hYB

end InfiniteMatroidCounterexample
end

end OAI


