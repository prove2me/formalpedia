-- Prove2me | Definitions.Def_RevenueOrdered_UDPmin_Pricing
-- name    : RevenueOrdered_UDPmin_Pricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:54:59.659816+00:00
-- url     : https://prove2.me/theorems/a525702f-b8d4-460f-9a30-1ee763dc5504
-- title:
--   Unit-demand min-pricing $\mathrm{UDP}_{\min}$: revenue, optimal revenue and uniform pricing
-- statement:
--   An instance of the **unit-demand envy-free min-pricing problem** $\mathrm{UDP}_{\min}$ has $n$ items and $m$ consumers. Consumer $i$ is interested in a set $B_i\subseteq[n]$ of items and has a valuation $v_i>0$, the most she is willing to pay for an item of $B_i$. Given a price assignment $p:[n]\to\mathbb R_{>0}$, consumer $i$ buys a cheapest item of $B_i$ if its price is at most $v_i$, and nothing otherwise; ties do not change what she pays. The seller's revenue is
--   $$\mathrm{rev}_{\mathrm{UDP}}(p)=\sum_{i\,:\,B_i\neq\emptyset,\ \min_{x\in B_i}p(x)\le v_i}\ \min_{x\in B_i}p(x).$$
--   The optimal revenue is $\mathrm{OPT}_{\mathrm{UDP}}=\sup_{p>0}\mathrm{rev}_{\mathrm{UDP}}(p)$, the supremum over all positive price assignments. **Uniform pricing** puts the same price $q>0$ on every item and chooses $q$ to maximise revenue; its value is
--   $$\mathrm{UP}=\sup_{q>0}\mathrm{rev}_{\mathrm{UDP}}(q,\dots,q).$$
--   Finally $v_{\max}$ and $v_{\min}$ are the largest and smallest valuations (the paper's $v_m$ and $v_1$ after sorting).
--
--   These are the objects of Lemma 4.5, Theorem 4.6 and Corollary 4.7.
--
--   **Formalization Note** Items and consumers are finite types `X` and `M`. The paper allows $v_i\ge 0$; here $v_i>0$ is a field of the instance, because the paper's own reduction needs revenues $m\cdot v>0$ and its ratio $v_m/v_1$ needs $v_1>0$. A consumer with $B_i=\emptyset$ pays $0$. Both suprema are real `⨆` over nonempty index sets (`p ≡ 1`, `q = 1`) whose revenues are bounded above by $\sum_i v_i$, so they are genuine suprema, not junk values.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 16 (§4.5, UDP_min and uniform pricing), p. 20 (Corollary 4.7, ρ := v_m/v_1)

import Mathlib

namespace RevenueOrdered.UDPmin

/-- An instance of the unit-demand min-pricing problem `UDP_min` (Berbeglia–Joret,
arXiv:1606.01371v3, §4.5, p. 16): items `X` (the paper's `[n]`), consumers `M` (the paper's
`[m]`); consumer `i` is interested in the items `B i ⊆ X` and has valuation `v i`. The paper
allows `v i ≥ 0`; here `v i > 0`, which the paper's own reduction (`r((x, v)) = m·v > 0`, p. 17)
and its ratio `ρ = v_m / v_1` require. -/
structure Instance (X M : Type*) where
  B : M → Finset X
  v : M → ℝ
  v_pos : ∀ i, 0 < v i

variable {X M : Type*} [Fintype X] [Fintype M]

/-- The amount consumer `i` pays under the price assignment `p`: the price of a cheapest item of
`B i` if that price is at most `v i`, and `0` otherwise (no purchase; in particular when
`B i = ∅`). Ties between cheapest items do not affect the amount. -/
noncomputable def payment (I : Instance X M) (p : X → ℝ) (i : M) : ℝ :=
  if h : (I.B i).Nonempty then
    if (I.B i).inf' h p ≤ I.v i then (I.B i).inf' h p else 0
  else 0

/-- The seller's revenue under the price assignment `p`: the sum of the consumers' payments. -/
noncomputable def revenue (I : Instance X M) (p : X → ℝ) : ℝ :=
  ∑ i, payment I p i

/-- `OPT_UDP`, the optimal revenue of the `UDP_min` instance: the supremum of `revenue I p` over
all positive price assignments `p : X → ℝ_{>0}`. The index set is nonempty and the revenue is
bounded above by `∑ i, v i`, so this is a genuine supremum. -/
noncomputable def optUDP (I : Instance X M) : ℝ :=
  ⨆ p : {p : X → ℝ // ∀ x, 0 < p x}, revenue I p.1

/-- The revenue of **uniform pricing** (p. 16): the supremum over all prices `q > 0` of the
revenue of the price assignment putting price `q` on every item. -/
noncomputable def uniformRevenue (I : Instance X M) : ℝ :=
  ⨆ q : {q : ℝ // 0 < q}, revenue I (fun _ => q.1)

/-- The largest valuation `v_m`. -/
noncomputable def vMax [Nonempty M] (I : Instance X M) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty I.v

/-- The smallest valuation `v_1`. -/
noncomputable def vMin [Nonempty M] (I : Instance X M) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty I.v

end RevenueOrdered.UDPmin


