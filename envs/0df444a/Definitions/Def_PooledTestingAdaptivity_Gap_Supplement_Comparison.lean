-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Comparison
-- name    : PooledTestingAdaptivity_Gap_Supplement_Comparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:36:46.087034+00:00
-- url     : https://prove2.me/theorems/0bea7144-16b0-4bfd-8c1f-e0997a2d9466
-- title:
--   Comparison quantities $q_t$, $u(t)$, $T_x$, $u^*$, $\Lambda$, $\varphi_G(\theta)$, $\mathrm{OPT}_{\mathrm{disj}}$ and the ratios $\mathcal A$, $\mathcal A_{\mathrm{disj}}$
-- statement:
--   Fix a standard-model instance $J$ with pool cap $G$ and a budget $B$.
--
--   1. For a set $t$ of individuals, $q_t=\prod_{i\in t}q_i$ (with $q_\emptyset=1$) and $u(t)=q_t\sum_{i\in t}u_i$ (with $u(\emptyset)=0$), the expected welfare of testing $t$ alone.
--   2. Let $m_i=u_iq_i$, ordered as $m_{(1)}\ge\dots\ge m_{(n)}$ and extended by zeros. For real $x\ge0$ the **fractional top sum** is
--   $$T_x=\sum_{k=1}^{\lfloor x\rfloor}m_{(k)}+(x-\lfloor x\rfloor)\,m_{(\lfloor x\rfloor+1)}.$$
--   3. $u^*=\max_{1\le|t|\le G}u(t)$ and $\Lambda=\max_{1\le|A|\le G}\sum_{i\in A}q_{A\setminus\{i\}}$, the maxima ranging over nonempty sets of at most $G$ individuals.
--   4. $\varphi_G(\theta)=\min_{s\in\{1,\dots,G\}}G/(s\theta^{s-1})$, and the middle term of Eq. (24) is $\min_{s\in\{1,\dots,G\}}\max\{1,\Lambda/s\}/\theta^{s-1}$.
--   5. $\mathrm{OPT}_{\mathrm{disj}}(B,J)$ is the supremum of static welfare over allocations in $\mathcal F_{B,G}$ whose pools are pairwise disjoint.
--   6. $\mathcal A(B,J)=\mathrm{OPT}_{\mathrm{dyn}}(B,J)/\mathrm{OPT}_{\mathrm{stat}}(B,J)$ and $\mathcal A_{\mathrm{disj}}(B,J)=\mathrm{OPT}_{\mathrm{dyn}}(B,J)/\mathrm{OPT}_{\mathrm{disj}}(B,J)$, each defined to be $1$ when its denominator is $0$, as in the paper.
--
--   These are the quantities of §§2.1 and 7.1 used by the master upper bounds and the boundary regimes.
--
--   **Formalization Note.** The sorted values are the multiset $\{m_i\}$ sorted in nonincreasing order; index $k$ of `mSorted` is $m_{(k+1)}$, and indices past $n$ give $0$. `topSum` is meant for $x\ge0$, the only arguments used ($B$ and $B\Lambda$).
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), §2.1, printed p. 5, PDF p. 6; §7 and §7.1, printed p. 23, PDF p. 24; Theorem 7.3 (iv), printed p. 24, PDF p. 25

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Greedy

namespace PooledTestingAdaptivity.Gap.Supplement

open Classical

/-- `q_t = ∏_{i ∈ t} q_i` (`q_∅ = 1`). -/
noncomputable def qProd {n : ℕ} (J : Instance n) (t : Finset (Fin n)) : ℝ :=
  ∏ i ∈ t, J.q i

/-- `u(t) = q_t Σ_{i ∈ t} u_i` (`u(∅) = 0`): the expected welfare of testing `t` alone. -/
noncomputable def poolValue {n : ℕ} (J : Instance n) (t : Finset (Fin n)) : ℝ :=
  qProd J t * ∑ i ∈ t, J.u i

/-- The values `m_i = u_i q_i` in nonincreasing order. -/
noncomputable def mList {n : ℕ} (J : Instance n) : List ℝ :=
  (((Finset.univ : Finset (Fin n)).val.map fun i => J.u i * J.q i).sort (· ≥ ·))

/-- `mSorted J k = m_(k+1)`: the `(k+1)`-st largest value of `m_i`, and `0` beyond `n`
(the sequence extended by zeros). -/
noncomputable def mSorted {n : ℕ} (J : Instance n) (k : ℕ) : ℝ :=
  (mList J).getD k 0

/-- §7.1 fractional top sum, for real `x ≥ 0`:
`T_x = Σ_{k=1}^{⌊x⌋} m_(k) + (x − ⌊x⌋) m_(⌊x⌋+1)`. -/
noncomputable def topSum {n : ℕ} (J : Instance n) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range ⌊x⌋₊, mSorted J k) + (x - ⌊x⌋₊) * mSorted J ⌊x⌋₊

/-- Nonempty sets of at most `G` individuals. -/
def poolSets {n : ℕ} (J : Instance n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun t => t.Nonempty ∧ t.card ≤ J.cap

theorem poolSets_nonempty {n : ℕ} (J : Instance n) : (poolSets J).Nonempty :=
  ⟨{⟨0, J.population_pos⟩}, by simp [poolSets]; exact J.cap_pos⟩

/-- `u* = max_{1 ≤ |t| ≤ G} u(t)`. -/
noncomputable def uStar {n : ℕ} (J : Instance n) : ℝ :=
  (poolSets J).sup' (poolSets_nonempty J) (poolValue J)

/-- `Λ = max_{1 ≤ |A| ≤ G} Σ_{i ∈ A} q_{A \ {i}}`. -/
noncomputable def Lambda {n : ℕ} (J : Instance n) : ℝ :=
  (poolSets J).sup' (poolSets_nonempty J) fun A => ∑ i ∈ A, qProd J (A.erase i)

theorem capRange_nonempty {n : ℕ} (J : Instance n) : (Finset.Icc 1 J.cap).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, J.cap_pos⟩⟩

/-- `min_{s ∈ {1,…,G}} max{1, Λ/s} / θ^{s−1}` (Eq. (24), middle term). -/
noncomputable def lambdaBound {n : ℕ} (J : Instance n) (θ : ℝ) : ℝ :=
  (Finset.Icc 1 J.cap).inf' (capRange_nonempty J) fun s => max 1 (Lambda J / s) / θ ^ (s - 1)

/-- `φ_G(θ) = min_{s ∈ {1,…,G}} G / (s θ^{s−1})`. -/
noncomputable def phiG {n : ℕ} (J : Instance n) (θ : ℝ) : ℝ :=
  (Finset.Icc 1 J.cap).inf' (capRange_nonempty J) fun s => (J.cap : ℝ) / (s * θ ^ (s - 1))

/-- `OPT_disj(B, J)`: the best static welfare over allocations of `F_{B,G}` whose pools
(at distinct list positions) are pairwise disjoint. -/
noncomputable def optDisj {n : ℕ} (J : Instance n) (B : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ T ∈ (standardFamily J B).allocations,
    T.Pairwise Disjoint ∧ staticWelfare J T = v}

/-- `A(B, J) = OPT_dyn / OPT_stat`, defined to be `1` when the denominator is `0`. -/
noncomputable def ratioA {n : ℕ} (J : Instance n) (B : ℕ) : ℝ :=
  if optStatic (standardFamily J B) = 0 then 1
  else optDynamic (standardFamily J B) / optStatic (standardFamily J B)

/-- `A_disj(B, J) = OPT_dyn / OPT_disj`, defined to be `1` when the denominator is `0`. -/
noncomputable def ratioDisj {n : ℕ} (J : Instance n) (B : ℕ) : ℝ :=
  if optDisj J B = 0 then 1 else optDynamic (standardFamily J B) / optDisj J B

end PooledTestingAdaptivity.Gap.Supplement


