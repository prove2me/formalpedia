-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
-- name    : OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:52:02.276789+00:00
-- url     : https://prove2.me/theorems/db8dee6f-9db8-479c-b0a6-8fdd971d6641
-- title:
--   Sparse perturbations: small subsets of a non-small pool that drive the probe to $+\infty$
-- statement:
--   Notation follows the block-density definitions: $D$ is the countable set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, $E_0=D\times\{0,1\}$, $W_m\subseteq E_0$ is the $m$-th block (the $2\cdot2^{2^m}$ elements $((m,g),b)$), $P_n=W_0\cup\dots\cup W_{n-1}$, and $\delta_m(X)=|X\cap W_m|/|W_m|$. A set $X\subseteq E_0$ is *small* if $\delta_m(X)\to0$, and $X$ lies in the *class* of $T$ if $X\triangle T$ is small. For $T,X\subseteq E_0$ write $d^T_m(X)=\delta_m(X)-\delta_m(T)$, $p^T_n(X)=|X\cap P_n|-|T\cap P_n|$, $e^T_n(X)=\sup_{m\ge n}|d^T_m(X)|$ for the error tail, and
--
--   $$\phi^T_n(X)=p^T_n(X)+|P_n|\Bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\Bigr)$$
--
--   for the probe.
--
--   The file contains no new definitions; it proves the following results.
--
--   1. **Strictly increasing choices.** If $\mathsf R(j,m)$ is a relation on $\mathbb N\times\mathbb N$ such that for all $j,M\in\mathbb N$ there is $m\ge M$ with $\mathsf R(j,m)$, then there is a strictly increasing sequence $(m_j)_{j\in\mathbb N}$ with $\mathsf R(j,m_j)$ for every $j$. Moreover the block sizes satisfy $|W_m|\to\infty$.
--   2. **Sparse spikes.** Let $G\subseteq E_0$ and $\delta>0$ be such that $\delta_m(G)\ge\delta$ for infinitely many $m$. Let $(b_j)$ be real numbers with $0<b_j\le\delta$ and $b_j\to0$, and let $(N_j)$ be any sequence of natural numbers. Then there is a small set $Q\subseteq G$ such that for every $j$ some $m\ge N_j$ satisfies $\delta_m(Q)\ge b_j$.
--   3. **Locating an index.** If $(N_j)$ is strictly increasing and $n\ge N_0$, then $N_j\le n<N_{j+1}$ for some $j$.
--   4. **Spike bound.** For all $T,X,Q\subseteq E_0$ with $X\cap Q=\emptyset$ and all $n\le m$,
--   $$p^T_n(X)+|P_n|\bigl(\delta_m(Q)-2e^T_n(X)\bigr)\le\phi^T_n(X\cup Q).$$
--   5. **Positive pool.** If $X$ lies in the class of $T$, $G$ is not small and $G\cap X=\emptyset$, then there is a small set $Q\subseteq G$ with
--   $$\lim_{n\to\infty}\phi^T_n(X\cup Q)=+\infty .$$
--
--   Because $Q$ is small, $X\cup Q$ stays in the class of $T$; so item 5 enlarges $X$ inside any non-small pool $G$ disjoint from $X$, without leaving the class, to a set whose probe lower limit is $+\infty$. Applied to complements, the same result yields deletions whose probe lower limit is $-\infty$. These are the extreme endpoints needed by the interpolation theorem for the lower local rule when the given interval does not already provide them.
--
--   **Formalization Note** The lemmas are `exists_strictMono_choice`, `block_card_atTop`, `exists_small_spikes` (its spike set is called `P`, and it carries the hypothesis `0 < δ` even though the construction does not use it), `strictMono_intervals`, `spike_probe_bound` (hypothesis `Disjoint X P`) and `positive_pool_add` (hypothesis `G ⊆ Xᶜ`, conclusion `Tendsto (fun n => fProbe T n (X ∪ P)) atTop atTop`). "Infinitely many $m$" is expressed as: for every `N` there is `m ≥ N`. The probe $\phi^T_n$ is `fProbe T n` and $e^T_n$ is `errorTail T X n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/SparsePerturbation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/SparsePerturbation.lean by skeleton subtraction
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

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma exists_strictMono_choice (P : ℕ → ℕ → Prop)
    (hP : ∀ j M, ∃ m, M ≤ m ∧ P j m) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ ∀ j, P j (m j) := by
  classical
  choose pick hpick using hP
  let m : ℕ → ℕ := Nat.rec (pick 0 0) (fun j prev ↦ pick (j+1) (prev+1))
  have he0 : m 0 = pick 0 0 := rfl
  have hes (j : ℕ) : m (j+1) = pick (j+1) (m j+1) := rfl
  refine ⟨m, strictMono_nat_of_lt_succ (fun j ↦ ?_), ?_⟩
  · rw [hes]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hpick (j+1) (m j+1)).1
  · intro j
    cases j with
    | zero => exact (hpick 0 0).2
    | succ j => exact (hpick (j+1) (m j+1)).2

lemma block_card_atTop : Tendsto (fun m ↦ ((wBlock m).card : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun m ↦ ?_) prefix_card_atTop
  have h := block_prefix_growth (le_refl m)
  exact_mod_cast (show (blockPrefix m).card ≤ (wBlock m).card by omega)

/-- A sparse collection of finite block selections with prescribed lower spikes. -/
lemma exists_small_spikes {G : Set E0} {δ : ℝ} (_hδ : 0 < δ)
    (hG : ∀ N, ∃ m, N ≤ m ∧ δ ≤ density G m)
    (b : ℕ → ℝ) (hbpos : ∀ j, 0 < b j) (hble : ∀ j, b j ≤ δ)
    (hbzero : Tendsto b atTop (𝓝 0)) (N : ℕ → ℕ) :
    ∃ P : Set E0, P ⊆ G ∧ Small P ∧ ∀ j, ∃ m, N j ≤ m ∧ b j ≤ density P m := by
  classical
  have hwzero : Tendsto (fun m ↦ (1:ℝ)/(wBlock m).card) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop block_card_atTop
  have hchoose : ∀ j M, ∃ m, M ≤ m ∧ N j ≤ m ∧ δ ≤ density G m ∧
      (1:ℝ)/(wBlock m).card ≤ b j := by
    intro j M
    obtain ⟨L,hL⟩ := eventually_atTop.mp (hwzero.eventually (gt_mem_nhds (hbpos j)))
    obtain ⟨m,hm,hGm⟩ := hG (max M (max (N j) L))
    refine ⟨m,(le_max_left _ _).trans hm,(le_max_left _ _).trans ((le_max_right _ _).trans hm),hGm,?_⟩
    exact (hL m ((le_max_right _ _).trans ((le_max_right _ _).trans hm))).le
  obtain ⟨m,hm,hmp⟩ := exists_strictMono_choice
    (fun j m ↦ N j ≤ m ∧ δ ≤ density G m ∧ (1:ℝ)/(wBlock m).card ≤ b j) hchoose
  have hwpos (j : ℕ) : (0:ℝ) < (wBlock (m j)).card := by rw [card_wBlock]; positivity
  have hselect (j : ℕ) : ∃ s : Finset E0, s ⊆ traceFinset (wBlock (m j)) G ∧
      s.card = ⌈b j * (wBlock (m j)).card⌉₊ := by
    apply Finset.exists_subset_card_eq
    apply Nat.ceil_le.mpr
    have hd := (hmp j).2.1
    change δ ≤ ((traceFinset (wBlock (m j)) G).card : ℝ) / (wBlock (m j)).card at hd
    exact (mul_le_mul_of_nonneg_right (hble j) (hwpos j).le).trans ((le_div_iff₀ (hwpos j)).mp hd)
  choose s hs hcard using hselect
  let P : Set E0 := ⋃ j, (s j : Set E0)
  have hP : P ⊆ G := by
    rintro x ⟨_,⟨j,rfl⟩,hx⟩
    exact ((mem_traceFinset _ _ _).mp (hs j hx)).2
  have hsm (j : ℕ) {x : E0} (hx : x ∈ s j) : x.1.1 = m j :=
    (mem_wBlock _ _).mp (((mem_traceFinset _ _ _).mp (hs j hx)).1)
  have htrace (j : ℕ) : traceFinset (wBlock (m j)) P = s j := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxw,hxP⟩ := mem_traceFinset _ _ _ |>.mp hx
      obtain ⟨i,hxi⟩ := mem_iUnion.mp hxP
      have he : i = j := hm.injective ((hsm i hxi).symm.trans ((mem_wBlock _ _).mp hxw))
      exact he ▸ hxi
    · intro hx
      exact (mem_traceFinset _ _ _).mpr ⟨(mem_wBlock _ _).mpr (hsm j hx), mem_iUnion.mpr ⟨j,hx⟩⟩
  have htrace0 (k : ℕ) (hk : k ∉ Set.range m) : traceFinset (wBlock k) P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxw,hxP⟩ := mem_traceFinset _ _ _ |>.mp hx
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hxP
    exact hk ⟨j,(hsm j hxj).symm.trans ((mem_wBlock _ _).mp hxw)⟩
  have hden (j : ℕ) : b j ≤ density P (m j) ∧ density P (m j) ≤ 2 * b j := by
    change b j ≤ ((traceFinset (wBlock (m j)) P).card : ℝ)/(wBlock (m j)).card ∧
      ((traceFinset (wBlock (m j)) P).card : ℝ)/(wBlock (m j)).card ≤ 2 * b j
    rw [htrace, hcard]
    constructor
    · exact (le_div_iff₀ (hwpos j)).mpr (Nat.le_ceil _)
    · have hc := Nat.ceil_lt_add_one (mul_nonneg (hbpos j).le (hwpos j).le)
      have hi := (div_le_iff₀ (hwpos j)).mp (hmp j).2.2
      apply (div_le_iff₀ (hwpos j)).mpr
      nlinarith
  have hsmall : Small P := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hb2 : Tendsto (fun j ↦ 2 * b j) atTop (𝓝 0) := by simpa using hbzero.const_mul 2
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (hb2.eventually (gt_mem_nhds hε))
    refine ⟨m J,fun k hk ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ density P k from finiteDensity_nonneg _ _)]
    by_cases hkr : k ∈ Set.range m
    · obtain ⟨j,rfl⟩ := hkr
      exact (hden j).2.trans_lt (hJ j (hm.le_iff_le.mp hk))
    · have hz : density P k = 0 := by simp [density,finiteDensity,htrace0 k hkr]
      rwa [hz]
  exact ⟨P,hP,hsmall,fun j ↦ ⟨m j,(hmp j).1,(hden j).1⟩⟩

lemma strictMono_intervals {N : ℕ → ℕ} (hN : StrictMono N) {n : ℕ} (hn : N 0 ≤ n) :
    ∃ j, N j ≤ n ∧ n < N (j+1) := by
  classical
  let j := Nat.findGreatest (fun j ↦ N j ≤ n) n
  refine ⟨j,Nat.findGreatest_spec (P := fun j ↦ N j ≤ n) (n := n) (Nat.zero_le n) hn,?_⟩
  by_contra! h
  exact Nat.findGreatest_is_greatest (show j < j+1 by omega)
    ((hN.id_le (j+1)).trans h) h

lemma spike_probe_bound {T X P : Set E0} (hXP : Disjoint X P) {n m : ℕ} (hnm : n ≤ m) :
    pProbe T X n + (blockPrefix n).card * (density P m - 2 * errorTail T X n) ≤
      fProbe T n (X ∪ P) := by
  have hsup := le_tailSup (dProbe_bddAbove T (X ∪ P)) hnm
  have heq : dProbe T (X ∪ P) m = dProbe T X m + density P m := by
    rw [dProbe, density, finiteDensity_union _ hXP]
    unfold dProbe density
    ring
  rw [heq] at hsup
  have hlow := (abs_le.mp ((abs_dProbe_le_errorTail T X hnm))).1
  have hinf : -errorTail T X n ≤ tailInf (dProbe T (X ∪ P)) n := by
    change -errorTail T X n ≤ sInf (dProbe T (X ∪ P) '' Ici n)
    apply le_csInf (tail_nonempty (dProbe T (X ∪ P)) n)
    rintro _ ⟨k,hk,rfl⟩
    exact ((abs_le.mp (abs_dProbe_le_errorTail T X hk)).1).trans
      (dProbe_mono T (Set.subset_union_left (s := X) (t := P)) k)
  have hp := pProbe_mono T (show X ⊆ X ∪ P from subset_union_left) n
  have ht : density P m - 2 * errorTail T X n ≤
      tailSup (dProbe T (X ∪ P)) n + tailInf (dProbe T (X ∪ P)) n := by linarith
  exact add_le_add hp (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))

lemma positive_pool_add {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ Xᶜ) :
    ∃ P, P ⊆ G ∧ Small P ∧ Tendsto (fun n ↦ fProbe T n (X ∪ P)) atTop atTop := by
  classical
  obtain ⟨δ,hδ,hδG⟩ := small_iff_density hG
  let b (j : ℕ) : ℝ := δ / (j+1:ℕ)
  have hbpos : ∀ j, 0 < b j := by intro j; dsimp [b]; positivity
  have hble : ∀ j, b j ≤ δ := by
    intro j
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (j+1:ℕ))).mpr
    have : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    nlinarith
  have hbzero : Tendsto b atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  let c (n : ℕ) : ℝ := (blockPrefix n).card
  let err (n : ℕ) : ℝ := |pProbe T X n| / c n + 2 * errorTail T X n + 1 / Real.sqrt (c n)
  have hE : Tendsto err atTop (𝓝 0) := by
    have hab : Tendsto (fun n ↦ |pProbe T X n| / c n) atTop (𝓝 0) := by
      simpa [c, abs_div] using (pProbe_normalized_zero hX).abs
    have hi : Tendsto (fun n ↦ (1:ℝ)/Real.sqrt (c n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp prefix_card_atTop)
    simpa only [zero_add,mul_zero,add_zero] using (hab.add ((errorTail_zero hX).const_mul 2)).add hi
  have hcut : ∀ j M, ∃ N, M ≤ N ∧ 1 ≤ N ∧ ∀ n, N ≤ n → err n ≤ b j := by
    intro j M
    obtain ⟨L,hL⟩ := eventually_atTop.mp (hE.eventually (gt_mem_nhds (hbpos j)))
    refine ⟨max M (max 1 L),le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),?_⟩
    exact fun n hn ↦ (hL n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))).le
  obtain ⟨N,hN,hNcut⟩ := exists_strictMono_choice
    (fun j N ↦ 1 ≤ N ∧ ∀ n, N ≤ n → err n ≤ b j) hcut
  obtain ⟨P,hPG,hP,hspike⟩ := exists_small_spikes hδ hδG b hbpos hble hbzero (fun j ↦ N (j+1))
  refine ⟨P,hPG,hP,?_⟩
  have hXP : Disjoint X P := Set.disjoint_left.mpr (fun _ hx hp ↦ hGX (hPG hp) hx)
  have hbound : ∀ᶠ n in atTop, Real.sqrt (c n) ≤ fProbe T n (X ∪ P) := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    obtain ⟨j,hjn,hnj⟩ := strictMono_intervals hN hn
    obtain ⟨m,hm,hbm⟩ := hspike j
    have hs := spike_probe_bound (T := T) hXP (hnj.le.trans hm)
    have hcn : 0 < c n := by
      have hn1 : 1 ≤ n := (hNcut 0).1.trans hn
      have hprefix : 1 ≤ (blockPrefix n).card := by
        have hx : (⟨⟨0,fun _ ↦ false⟩,false⟩ : E0) ∈ blockPrefix n := (mem_prefix _ _).mpr (by change 0 < n; omega)
        exact Finset.card_pos.mpr ⟨_,hx⟩
      change (0:ℝ) < ((blockPrefix n).card : ℝ)
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hprefix)
    have he := (hNcut j).2 n hjn
    change |pProbe T X n| / c n + 2 * errorTail T X n + 1 / Real.sqrt (c n) ≤ b j at he
    have hsqrt : 0 < Real.sqrt (c n) := Real.sqrt_pos.2 hcn
    have hid : c n / Real.sqrt (c n) = Real.sqrt (c n) := by
      apply (div_eq_iff hsqrt.ne').mpr
      simpa only [pow_two] using (Real.sq_sqrt hcn.le).symm
    have hem := mul_le_mul_of_nonneg_right he hcn.le
    have hcne := hcn.ne'
    change pProbe T X n + c n * (density P m - 2 * errorTail T X n) ≤ _ at hs
    have hpabs := neg_abs_le (pProbe T X n)
    have hbmult := mul_le_mul_of_nonneg_left hbm hcn.le
    rw [add_mul, add_mul, div_mul_cancel₀ _ hcne] at hem
    have hm2 : (1 / Real.sqrt (c n)) * c n = Real.sqrt (c n) := by
      rw [one_div, inv_mul_eq_div, hid]
    rw [hm2] at hem
    nlinarith
  exact tendsto_atTop_mono' atTop hbound (Real.tendsto_sqrt_atTop.comp prefix_card_atTop)

end InfiniteMatroidCounterexample
end

end OAI


