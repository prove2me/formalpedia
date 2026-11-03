-- Prove2me | Definitions.Def_MultiPurchaseMNL_ValueFunction
-- name    : MultiPurchaseMNL_ValueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:02.92503+00:00
-- url     : https://prove2.me/theorems/dc11fbb1-3442-4255-8bb1-784a0b09cddb
-- title:
--   §2.2, §4.1–§4.2, pp.11, 17–18 — Lemma 1's recursion, the light set $L$, the family $\mathcal F$, the value function $V$ (4), the proxies $\tilde\pi_i$
-- statement:
--   Four objects of the analysis.
--
--   1. The right-hand side of Lemma 1 as a recursion: $\hat\pi_0(i,S)=0$ and
--   $$
--   \hat\pi_{m+1}(i,S)=\frac{w_i+\sum_{j\in S_{-i}}w_j\,\hat\pi_m(i,S_{-j})}{1+w(S)} .
--   $$
--   2. For a set $H$ of heavy products, the light products $L=\{i\in[n]\setminus H: w_i\le\min_{j\in H}w_j\}$ (§4.1) and, for a guess $W$ and accuracy $\delta$, the family
--   $$
--   \mathcal F=\Big\{S\subseteq L\cup H:\ w(S\cap L)\in\Big[\tfrac{W}{(1+\delta)^2},(1+\delta)W\Big],\ S\supseteq H\Big\}.
--   $$
--   3. The value function (4): $V(i,0,H)=0$ and
--   $$
--   V(i,m,H)=\frac{1}{1+(1+\delta)W+w(H)}\Big(w_i+\Big[\tfrac{W}{(1+\delta)^2}-\delta\, w(H_{-i})\Big]^+ V(i,m-1,H)+\sum_{j\in H_{-i}}w_j\,V(i,m-1,H_{-j})\Big).
--   $$
--   4. The proxies $\tilde\pi_i=\mathbb E[V(i,M,H)]=\sum_m\Pr[M=m]\,V(i,m,H)$.
--
--   These are the quantities of Claims 2–3, Lemma 5 and the knapsack reduction (5)–(6).
--
--   **Formalization Note** $S_{-j}$ is `S.erase j` and $[x]^+$ is `max 0 x`. The light set is written with $\forall j\in H,\ w_i\le w_j$, which equals the paper's set for nonempty $H$. $V$ is defined for every $i$, $m$ and $H$.
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §2.2, p.11 (Lemma 1); §4.1, p.17; §4.2, p.18, (4), Lemma 5

import Mathlib
import Definitions.Def_MultiPurchaseMNL_Model

namespace MultiPurchaseMNL

variable {n mmax : ℕ}

/-- **The recursion of Lemma 1**, §2.2, p.11, as a pure function:
`π̂₀(i, S) = 0` and
`π̂ₘ₊₁(i, S) = (wᵢ + Σ_{j∈S−i} wⱼ · π̂ₘ(i, S−j)) / (1 + w(S))`.
Lemma 1 asserts `πₘ = π̂ₘ` for `i ∈ S`; here it is only the right-hand side, not the model.

**Formalization Note.** `S−j` is `S.erase j`. The base case is the paper's `π₀ = 0`. -/
noncomputable def piRec (I : Instance n mmax) (i : Fin n) : ℕ → Finset (Fin n) → ℝ
  | 0, _ => 0
  | m + 1, S =>
      (I.w i + ∑ j ∈ S.erase i, I.w j * piRec I i m (S.erase j)) / (1 + wsum I S)

/-- **The light products** for a set `H` of heavy products, §4.1, p.17:
`L = {i ∈ [n] \ H : wᵢ ≤ min_{j∈H} wⱼ}`.

**Formalization Note.** `wᵢ ≤ min_{j∈H} wⱼ` is written `∀ j ∈ H, wᵢ ≤ wⱼ`; the two agree for
nonempty `H`, which is the only case the paper uses (`|H*| = N ≥ 1`). -/
noncomputable def light (I : Instance n mmax) (H : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ∉ H ∧ ∀ j ∈ H, I.w i ≤ I.w j

/-- **The family `F`**, §4.2, p.18:
`F = {S ⊆ L ∪ H* : w(S ∩ L) ∈ [W/(1+δ)², (1+δ)·W], S ⊇ H*}`, for the heavy set `H` (the paper's
`H*`), its light set `L = light I H`, the guess `W` and the accuracy `δ`. -/
def InF (I : Instance n mmax) (H : Finset (Fin n)) (δ W : ℝ) (S : Finset (Fin n)) : Prop :=
  S ⊆ H ∪ light I H ∧ H ⊆ S ∧
    W / (1 + δ) ^ 2 ≤ wsum I (S ∩ light I H) ∧ wsum I (S ∩ light I H) ≤ (1 + δ) * W

/-- **The value function (4)**, §4.2, p.18:
`V(i, m, H) = 1/(1 + (1+δ)·W + w(H)) · (wᵢ + [W/(1+δ)² − δ·w(H₋ᵢ)]⁺ · V(i, m−1, H)
  + Σ_{j∈H₋ᵢ} wⱼ · V(i, m−1, H₋ⱼ))`, with base cases `V(·, 0, ·) = 0`.

**Formalization Note.** `[x]⁺ = max 0 x`, `H₋ᵢ = H.erase i`. Defined for every product `i`, every
`m : ℕ` and every set `H`; the paper uses `m ∈ [m_max]₀` and `H ⊆ H*`. -/
noncomputable def V (I : Instance n mmax) (δ W : ℝ) (i : Fin n) : ℕ → Finset (Fin n) → ℝ
  | 0, _ => 0
  | m + 1, H =>
      (I.w i + max 0 (W / (1 + δ) ^ 2 - δ * wsum I (H.erase i)) * V I δ W i m H +
          ∑ j ∈ H.erase i, I.w j * V I δ W i m (H.erase j)) /
        (1 + (1 + δ) * W + wsum I H)

/-- **The proxies** `π̃ᵢ = E[V(i, M, H*)] = Σₘ Pr[M = m] · V(i, m, H*)`, §4.2, p.18 (Lemma 5 and
"Constructing the knapsack problem"). The expectation is over `M` only. -/
noncomputable def proxy (I : Instance n mmax) (δ W : ℝ) (H : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ m : Fin (mmax + 1), I.p m * V I δ W i m H

end MultiPurchaseMNL


