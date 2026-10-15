-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:30:24.034128+00:00
-- url     : https://prove2.me/theorems/517fefad-1a63-44c8-8dfd-16d55d4728c7
-- title:
--   Probe error terms in a density class: block sums, error tails and density spikes
-- statement:
--   Notation follows the block-density definitions. Let $D$ be the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ a Boolean function of $m$ variables, and let $E_0=D\times\{0,1\}$. The $m$-th block $W_m\subseteq E_0$ consists of the $2\cdot 2^{2^m}$ elements $((m,g),b)$, and $P_n=W_0\cup\dots\cup W_{n-1}$ is the $n$-th prefix. For a finite set $s$ and any set $X$ put $\delta_s(X)=|X\cap s|/|s|$, and write $\delta_m(X)=\delta_{W_m}(X)$ for the density of $X$ in the $m$-th block. A set $X\subseteq E_0$ is *small* if $\delta_m(X)\to0$ as $m\to\infty$, and $X$ lies in the *class* of $T\subseteq E_0$ if the symmetric difference $X\triangle T$ is small. For $T,X\subseteq E_0$ the block and prefix differences are
--
--   $$
--   d^T_m(X)=\delta_m(X)-\delta_m(T),\qquad p^T_n(X)=|X\cap P_n|-|T\cap P_n|,
--   $$
--
--   and the probe of $X$ relative to $T$ is $\phi^T_n(X)=p^T_n(X)+|P_n|\bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\bigr)$.
--
--   The file introduces one new object.
--
--   1. **Error tail.** For $T,X\subseteq E_0$ and $n\in\mathbb N$,
--   $$e^T_n(X)=\sup_{m\ge n}\bigl|d^T_m(X)\bigr| .$$
--   Because $|d^T_m(X)|\le1$ for every $m$, this supremum is finite, and $|d^T_m(X)|\le e^T_n(X)$ whenever $n\le m$.
--
--   It also proves the following facts.
--
--   - *Density comparison.* For every finite set $s$ (of any type) and all sets $X,Y$: $|\delta_s(X)-\delta_s(Y)|\le\delta_s(X\triangle Y)$.
--   - *Block decomposition.* For every $X\subseteq E_0$ and every $n$, $|X\cap P_n|=\sum_{m<n}|X\cap W_m|$; consequently $p^T_n(X)=\sum_{m<n}|W_m|\,d^T_m(X)$ for all $T,X$. Moreover $|P_n|\to\infty$.
--   - *Behaviour inside a class.* If $X$ lies in the class of $T$, then
--   $$\lim_{m\to\infty}d^T_m(X)=0,\qquad \lim_{n\to\infty}e^T_n(X)=0,\qquad \lim_{n\to\infty}\frac{p^T_n(X)}{|P_n|}=0 .$$
--   - *Density spikes.* If $G\subseteq E_0$ is not small, then there is $\delta>0$ such that for every $N\in\mathbb N$ some $m\ge N$ satisfies $\delta_m(G)\ge\delta$.
--
--   These are the error estimates for the probe. For a set $X$ in the class of $T$, both the normalized prefix term $p^T_n(X)/|P_n|$ and the oscillation $e^T_n(X)$ of the block differences beyond $n$ become negligible, while a non-small pool $G$ has blocks of density bounded below infinitely often. The sparse-perturbation argument combines them: it adds to $X$ a small set of density spikes taken from $G$, so that the probe tends to $+\infty$ while the class of $X$ does not change.
--
--   **Formalization Note** `errorTail T X n` is `tailSup (fun m => |dProbe T X m|) n`, the `sSup` of the values at indices $m\ge n$; the bound `dProbe_abs_bdd` makes it the usual supremum (`abs_dProbe_le_errorTail`). `finiteDensity s X` is `(traceFinset s X).card / s.card`, which is $0$ for an empty `s` by Lean's convention for division by zero; accordingly `finiteDensity_abs_sub` holds for every finset, and the quotient $p^T_0(X)/|P_0|$ equals $0$ because $P_0=\emptyset$, which does not affect the limit in `pProbe_normalized_zero`. The remaining lemmas are `dProbe_zero`, `trace_prefix_card`, `prefix_card_atTop`, `pProbe_sum` and `errorTail_zero`. Despite its name, `small_iff_density` proves only the implication from non-smallness to the existence of density spikes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/ProbeLimits.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/ProbeLimits.lean by skeleton subtraction
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

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma finiteDensity_abs_sub {α : Type*} (s : Finset α) (X Y : Set α) :
    |finiteDensity s X - finiteDensity s Y| ≤ finiteDensity s (X ∆ Y) := by
  apply abs_le.mpr
  constructor
  · have h := (finiteDensity_mono s (show Y ⊆ X ∪ (X ∆ Y) by
      intro x hy; by_cases hx : x ∈ X; exact Or.inl hx
      exact Or.inr (by simp [symmDiff_def, hy, hx]))).trans (finiteDensity_union_le s X (X ∆ Y))
    linarith
  · have h := (finiteDensity_mono s (show X ⊆ Y ∪ (X ∆ Y) by
      intro x hx; by_cases hy : x ∈ Y; exact Or.inl hy
      exact Or.inr (by simp [symmDiff_def, hy, hx]))).trans (finiteDensity_union_le s Y (X ∆ Y))
    linarith

lemma dProbe_zero {T X : Set E0} (hX : SameClass T X) :
    Tendsto (dProbe T X) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero (fun _ ↦ abs_nonneg _) (fun m ↦ finiteDensity_abs_sub (wBlock m) X T) hX

lemma trace_prefix_card (X : Set E0) (n : ℕ) :
    (traceFinset (blockPrefix n) X).card = ∑ m ∈ range n, (traceFinset (wBlock m) X).card := by
  classical
  have he : traceFinset (blockPrefix n) X = (range n).biUnion (fun m ↦ traceFinset (wBlock m) X) := by
    ext x
    simp [mem_prefix]
  rw [he]
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact (wBlock_disjoint hij).mono (traceFinset_subset _ _) (traceFinset_subset _ _)

lemma prefix_card_atTop : Tendsto (fun n ↦ ((blockPrefix n).card : ℝ)) atTop atTop := by
  have h : ∀ n, n ≤ (blockPrefix n).card := by
    intro n
    rw [card_prefix]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have : 1 ≤ (wBlock n).card := by apply Nat.succ_le_of_lt; rw [card_wBlock]; positivity
      omega
  apply tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast h n

lemma pProbe_sum (T X : Set E0) (n : ℕ) :
    pProbe T X n = ∑ m ∈ range n, ((wBlock m).card : ℝ) * dProbe T X m := by
  rw [pProbe, trace_prefix_card, trace_prefix_card]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hc : ((wBlock m).card : ℝ) ≠ 0 := by simp
  simp only [dProbe, density, finiteDensity]
  field_simp

lemma pProbe_normalized_zero {T X : Set E0} (hX : SameClass T X) :
    Tendsto (fun n ↦ pProbe T X n / (blockPrefix n).card) atTop (𝓝 0) := by
  have hc : Tendsto (fun n ↦ ∑ m ∈ range n, ((wBlock m).card : ℝ)) atTop atTop := by
    simpa only [card_prefix, Nat.cast_sum] using prefix_card_atTop
  simpa only [pProbe_sum, card_prefix, Nat.cast_sum] using
    weighted_mean_zero (fun m ↦ ((wBlock m).card : ℝ)) (dProbe T X)
      (fun _ ↦ Nat.cast_nonneg _) hc (dProbe_zero hX)

noncomputable def errorTail (T X : Set E0) (n : ℕ) : ℝ := tailSup (fun m ↦ |dProbe T X m|) n

lemma dProbe_abs_bdd (T X : Set E0) : BddAbove (Set.range (fun m ↦ |dProbe T X m|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact abs_le.mpr (dProbe_bounds T X m)

lemma abs_dProbe_le_errorTail (T X : Set E0) {n m : ℕ} (hnm : n ≤ m) :
    |dProbe T X m| ≤ errorTail T X n := le_tailSup (dProbe_abs_bdd T X) hnm

lemma errorTail_zero {T X : Set E0} (hX : SameClass T X) :
    Tendsto (errorTail T X) atTop (𝓝 0) :=
  tail_absSup_zero _ (dProbe_abs_bdd T X) (dProbe_zero hX)

lemma small_iff_density {G : Set E0} (hG : ¬ Small G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ m, N ≤ m ∧ δ ≤ density G m := by
  by_contra! hn
  apply hG
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hn ε hε
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ density G m from finiteDensity_nonneg _ _)]
  exact hN m hm

end InfiniteMatroidCounterexample
end

end OAI


