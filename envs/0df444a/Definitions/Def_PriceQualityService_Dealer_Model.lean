-- Prove2me | Definitions.Def_PriceQualityService_Dealer_Model
-- name    : PriceQualityService_Dealer_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:20.634827+00:00
-- url     : https://prove2.me/theorems/c7443a81-d468-4363-ac31-f17c30919cb5
-- title:
--   The dealer's MNL choice probabilities (12) and profit $\Pi^s(\mathbf p,\mathbf q;S_l,S_s)$ (13)
-- statement:
--   A dealer carries products $\mathcal N=\{1,\dots,N\}$ whose prices $p_i$ and quality levels $q_i$ are fixed by the manufacturers. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ (unit production cost $c_iq_i^2$) and service cost per unit time $a_i-b_iq_i$. Two service durations $t_s$ (short) and $t_l$ (long) are available. The dealer chooses two disjoint sets $S_l,S_s\subseteq\mathcal N$: products in $S_l$ are offered with service duration $t_l$, products in $S_s$ with $t_s$, and products in neither are not offered.
--
--   The **attraction** of product $i$ with duration $t$ is $\exp(\alpha_iq_i-p_i+ts_i)$, and its **markup** is $p_i-c_iq_i^2-t(a_i-b_iq_i)$. Under the multinomial logit model with an outside option, the choice probability of product $i$ is
--
--   $$
--   d_i(\mathbf p,\mathbf q;S_l,S_s)=\begin{cases}\dfrac{\exp(\alpha_iq_i-p_i+t_ls_i)}{1+\sum_{j\in S_l}\exp(\alpha_jq_j-p_j+t_ls_j)+\sum_{j\in S_s}\exp(\alpha_jq_j-p_j+t_ss_j)}, & i\in S_l,\\[2ex] \dfrac{\exp(\alpha_iq_i-p_i+t_ss_i)}{1+\sum_{j\in S_l}\exp(\alpha_jq_j-p_j+t_ls_j)+\sum_{j\in S_s}\exp(\alpha_jq_j-p_j+t_ss_j)}, & i\in S_s,\end{cases}
--   $$
--
--   and $0$ for a product that is not offered. With the market size normalized to one, the dealer's expected profit is
--
--   $$
--   \Pi^s(\mathbf p,\mathbf q;S_l,S_s)=\sum_{i\in S_l}\big[p_i-c_iq_i^2-t_l(a_i-b_iq_i)\big]\,d_i(\mathbf p,\mathbf q;S_l,S_s)+\sum_{i\in S_s}\big[p_i-c_iq_i^2-t_s(a_i-b_iq_i)\big]\,d_i(\mathbf p,\mathbf q;S_l,S_s).
--   $$
--
--   These are the objects of the dealer's assortment and service-attachment problem (13): maximize $\Pi^s$ over disjoint pairs $(S_l,S_s)$.
--
--   **Formalization Note** Products are indexed by `Fin N` (0-based) and the parameters are arbitrary real vectors; the outside option is the constant `1` in the denominator, not an element of `Fin N`. The MNL form is taken as the definition; its derivation from i.i.d. Gumbel utilities (McFadden 1974) is cited by the paper, not formalized. The paper defines (12) only for disjoint $S_l,S_s$; on an overlapping pair the long-service branch is used, a value no theorem of the mission depends on.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 22, eqs. (11)–(13); p. 7, eq. (2); pp. 8–9, cost model

import Mathlib

namespace PriceQualityService.Dealer

open Finset

/-- The MNL attraction weight `exp(α_i q_i − p_i + t s_i)` of product `i` (indexed by `Fin N`,
0-based) when it is sold at the fixed price `p i` and quality `q i` with service duration `t`
(Wang, Ke & Cui, eq. (11)–(12), p. 22). The paper derives the MNL form from i.i.d. Gumbel
utilities (McFadden 1974); that derivation is cited, not formalized: the choice probabilities
below are *defined* by the closed form (12). -/
noncomputable def attraction {N : ℕ} (α s p q : Fin N → ℝ) (t : ℝ) (i : Fin N) : ℝ :=
  Real.exp (α i * q i - p i + t * s i)

/-- The markup (profit margin) of product `i` sold with service duration `t`:
`p_i − c_i q_i² − t (a_i − b_i q_i)` (the brackets of (13), p. 22). -/
def markup {N : ℕ} (a b c p q : Fin N → ℝ) (t : ℝ) (i : Fin N) : ℝ :=
  p i - c i * q i ^ 2 - t * (a i - b i * q i)

/-- The common denominator of (12): `1 + ∑_{j ∈ S_l} exp(α_j q_j − p_j + t_l s_j)
+ ∑_{j ∈ S_s} exp(α_j q_j − p_j + t_s s_j)`; the `1` is the outside option. -/
noncomputable def choiceDenom {N : ℕ} (α s p q : Fin N → ℝ) (ts tl : ℝ)
    (Sl Ss : Finset (Fin N)) : ℝ :=
  1 + ∑ j ∈ Sl, attraction α s p q tl j + ∑ j ∈ Ss, attraction α s p q ts j

/-- The MNL choice probability (12), p. 22, of product `i` when the products in `Sl` are offered
with the long service duration `tl` and those in `Ss` with the short duration `ts`. A product in
neither set is not offered and gets probability `0`. (The paper only defines (12) for disjoint
`Sl`, `Ss`; on a non-disjoint pair the `Sl` branch wins, a value no theorem of the mission uses.) -/
noncomputable def choiceProb {N : ℕ} (α s p q : Fin N → ℝ) (ts tl : ℝ)
    (Sl Ss : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ Sl then attraction α s p q tl i / choiceDenom α s p q ts tl Sl Ss
  else if i ∈ Ss then attraction α s p q ts i / choiceDenom α s p q ts tl Sl Ss
  else 0

/-- The dealer's expected profit Π^s(p, q; S_l, S_s) of (13), p. 22 (market size normalized
to one): `∑_{i ∈ S_l} [p_i − c_i q_i² − t_l(a_i − b_i q_i)] d_i + ∑_{i ∈ S_s} [p_i − c_i q_i²
− t_s(a_i − b_i q_i)] d_i`. -/
noncomputable def dealerProfit {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ)
    (Sl Ss : Finset (Fin N)) : ℝ :=
  ∑ i ∈ Sl, markup a b c p q tl i * choiceProb α s p q ts tl Sl Ss i +
    ∑ i ∈ Ss, markup a b c p q ts i * choiceProb α s p q ts tl Sl Ss i

end PriceQualityService.Dealer


