-- Prove2me | Definitions.Def_FirstPriceLearning_Stochastic_Auction
-- name    : FirstPriceLearning_Stochastic_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:13.591902+00:00
-- url     : https://prove2.me/theorems/0c7eefd3-9b94-4074-ad89-7e5952cd8aac
-- title:
--   §2.2 and (6), pp. 9, 19–20 — repeated first-price auction: payoff (1), expected reward (2), regret (3), quantization grids
-- statement:
--   A single bidder takes part in $T$ repeated first-price auctions. In round $t$ she has a private value $v_t\in[0,1]$, bids $b_t\in[0,1]$, and the highest other bid (HOB) is $m_t\in[0,1]$. She wins iff $b_t\ge m_t$, and then pays her bid, so her payoff is
--
--   $$
--   r(v_t,b_t;m_t)=(v_t-b_t)\,\mathbb 1(b_t\ge m_t). \qquad (1)
--   $$
--
--   The HOBs are iid with an unknown cumulative distribution function $G(x)=\mathbb P(m_t\le x)$ on $[0,1]$, with no smoothness or shape assumption (atoms are allowed). The expected reward of the bid $b$ at value $v$ and the regret of a bid sequence $b=(b_t)$ against a value sequence $v=(v_t)$ are
--
--   $$
--   R(v,b)=(v-b)\,G(b)\quad(2),\qquad R_T(\pi;v)=\sum_{t=1}^T\Big(\max_{b\in[0,1]}R(v_t,b)-R(v_t,b_t)\Big)\quad(3).
--   $$
--
--   For the reduction of §3.4 the file also defines the quantized context and action sets
--
--   $$
--   \mathcal C=\{1/M,2/M,\dots,1\},\qquad \mathcal A=\{1/K,2/K,\dots,1\}, \qquad (6)
--   $$
--
--   the clipped value $\tilde v=\min\{x\in\mathcal C: x\ge v\}$, the quantized regret $\tilde R_T=\sum_t(\max_{b\in\mathcal A}R(\tilde v_t,b)-R(\tilde v_t,b_t))$ of Lemma 4, and the largest maximiser $b^\star(v)$ of $R(v,\cdot)$ over a finite set of bids (Lemma 5).
--
--   These are the objects every result of the mission is stated in.
--
--   **Formalization Note.** $G$ is given by its law `μG` on $\mathbb R$ (a probability measure with $\mu_G([0,1]^c)=0$ in every theorem), and $G(x)=\mu_G((-\infty,x])$. The maximum over $[0,1]$ is a real supremum over the nonempty interval, on which $R(v,\cdot)$ is bounded; it is attained. Rounds are indexed by `Fin T`; paper round $t$ is index $t-1$. $\tilde v$ is a real infimum of a finite set, nonempty whenever $v\le 1$ and $M\ge1$. The largest maximiser is $0$ on an empty set of bids, a case no theorem uses.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 9, (1)–(3); p. 19, (6); p. 20, Lemmas 4–5

import Mathlib

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- The CDF of the highest-other-bid (HOB) law `μG`: `G(x) = P(m ≤ x)` (p. 9). -/
noncomputable def cdf (μG : Measure ℝ) (x : ℝ) : ℝ :=
  (μG (Set.Iic x)).toReal

/-- The instantaneous payoff (1): `r(v, b; m) = (v - b) 𝟙(b ≥ m)`. -/
noncomputable def payoff (v b m : ℝ) : ℝ :=
  (v - b) * (if m ≤ b then 1 else 0)

/-- The expected reward (2): `R(v, b) = (v - b) G(b)`. -/
noncomputable def expReward (μG : Measure ℝ) (v b : ℝ) : ℝ :=
  (v - b) * cdf μG b

/-- The oracle reward `max_{b ∈ [0,1]} R(v, b)`, written as a supremum over the bids in `[0, 1]`
(the set is nonempty, the function is bounded on it, and the maximum is attained). -/
noncomputable def oracle (μG : Measure ℝ) (v : ℝ) : ℝ :=
  ⨆ b : Set.Icc (0 : ℝ) 1, expReward μG v b

/-- The regret (3) of the bid sequence `b` against the value sequence `v` over `T` rounds:
`R_T = ∑_{t=1}^T (max_{b ∈ [0,1]} R(v_t, b) - R(v_t, b_t))`. Round `t` of the paper is the
index `t.val + 1`. -/
noncomputable def regret (μG : Measure ℝ) {T : ℕ} (v b : Fin T → ℝ) : ℝ :=
  ∑ t, (oracle μG (v t) - expReward μG (v t) (b t))

/-- The quantized context set (6): `𝒞 = {1/M, 2/M, …, 1}`. -/
noncomputable def gridC (M : ℕ) : Finset ℝ :=
  (Finset.range M).image (fun i : ℕ => ((i : ℝ) + 1) / M)

/-- The quantized action (bid) set (6): `𝒜 = {1/K, 2/K, …, 1}`. -/
noncomputable def gridA (K : ℕ) : Finset ℝ :=
  (Finset.range K).image (fun j : ℕ => ((j : ℝ) + 1) / K)

/-- The clipped value `ṽ = min {x ∈ 𝒞 : x ≥ v}` (p. 20). It is the least element of a nonempty
finite set whenever `v ≤ 1` and `M ≥ 1`. -/
noncomputable def clipValue (M : ℕ) (v : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ gridC M ∧ v ≤ x}

/-- The regret `R̃_T(π^Q, v) = ∑_t (max_{b ∈ A} R(ṽ_t, b) - R(ṽ_t, b_t))` of a bid sequence on the
grid `A`, against the clipped values `vq` (Lemma 4, p. 20). -/
noncomputable def gridRegret (μG : Measure ℝ) (A : Finset ℝ) {T : ℕ} (vq b : Fin T → ℝ) : ℝ :=
  ∑ t, ((⨆ x : A, expReward μG (vq t) x) - expReward μG (vq t) (b t))

open scoped Classical in
/-- The largest maximiser `b⋆(v)` of `b ↦ R(v, b)` over a finite set `A` of bids (Lemma 5,
p. 20). For empty `A` it is `0` (never used: the grid (6) is nonempty for `K ≥ 1`). -/
noncomputable def largestMaximizer (μG : Measure ℝ) (A : Finset ℝ) (v : ℝ) : ℝ :=
  if h : A.Nonempty then
    (A.filter (fun b => ∀ b' ∈ A, expReward μG v b' ≤ expReward μG v b)).max'
      (by
        obtain ⟨b, hb, hmax⟩ := A.exists_max_image (expReward μG v) h
        exact ⟨b, Finset.mem_filter.mpr ⟨hb, hmax⟩⟩)
  else 0

end FirstPriceLearning.Stochastic


