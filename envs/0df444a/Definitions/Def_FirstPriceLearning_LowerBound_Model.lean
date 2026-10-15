-- Prove2me | Definitions.Def_FirstPriceLearning_LowerBound_Model
-- name    : FirstPriceLearning_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:45.876753+00:00
-- url     : https://prove2.me/theorems/6a7567ea-ef48-4202-9045-9442fb926bba
-- title:
--   Repeated first-price auction with full information: reward $(v-b)G(b)$, regret (3), randomized policies
-- statement:
--   This module fixes the repeated first-price auction model of §2.2 in the full-information setting of Theorem 9.
--
--   1. **HOB law and CDF.** The highest other bid $m$ has law $\mu_G$, a measure on $\mathbb R$, and $G(x)=\mathbb P(m\le x)=\mu_G((-\infty,x])$.
--   2. **Payoff (1).** A bidder with value $v$ who bids $b$ receives $r(v,b;m)=(v-b)\mathbb 1(b\ge m)$.
--   3. **Expected reward (2).** $R(v,b)=(v-b)G(b)$.
--   4. **Oracle and regret (3).** For values $v_1,\dots,v_T$ and bids $b_1,\dots,b_T$,
--   $$
--   R_T(\pi;v)=\sum_{t=1}^T\Bigl(\max_{b\in[0,1]}R(v_t,b)-R(v_t,b_t)\Bigr),
--   $$
--   with the maximum written as the supremum over $b\in[0,1]$.
--   5. **Full-information randomized policies.** A policy $\pi$ for horizon $T$ draws internal randomness $u\sim\mu_U$ from a probability space $(U,\mu_U)$; its bid at round $t$ is $b_t=\beta_t(u,m_1,\dots,m_{t-1})\in[0,1]$, a jointly measurable function of $u$ and the HOBs revealed in the earlier rounds. Values are $v_t\equiv1$ in Theorem 9, so they are not an input.
--   6. **Expected regret.** $\mathbb E_G[R_T(\pi;v)]$ with $v_t\equiv1$ is the integral of $R_T$ over $u\sim\mu_U$ and $m_1,\dots,m_T$ iid from $G$, independent of $u$.
--
--   These are the objects in terms of which the lower bound of Theorem 9 and its two-point reduction (21) are stated.
--
--   **Formalization Note** Rounds are indexed by `Fin T`; Lean round `t` is paper time $t+1$, and the bid at round `t` receives the history $(m_1,\dots,m_{t-1})$ as a function on `Fin t`, so a policy cannot see $m_t$ or later HOBs. The supremum in the oracle is over a nonempty family bounded above, so it is the true maximum value. The bid maps are required to be jointly measurable; otherwise the expectation would not be defined. The internal randomness space lives in `Type`. The payoff (1) is included for reference; `Solutions/verification` checks that $R(v,b)=\int r(v,b;m)\,dG(m)$ for a probability law.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, pp. 8–9, §2.2, (1)–(3); p. 36, Theorem 9 (full information, v_t ≡ 1)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- A randomized, non-anticipating bidding policy for horizon `T` under **full information** (the HOB
`m_s` is revealed at the end of every round `s`), as in Theorem 9 (p. 36), where the values are
`v_t ≡ 1` and therefore not an input. The policy draws its internal randomness `u` from the
probability measure `μU` on `U`; the bid at round `t` (paper time `t.val + 1`) is a jointly measurable
function `bid t u (m_1, …, m_{t−1})` of `u` and the HOBs observed so far, with values in `[0, 1]`. -/
structure FullInfoPolicy (T : ℕ) (U : Type) [MeasurableSpace U] where
  /-- the law of the internal randomness -/
  μU : Measure U
  isProb : IsProbabilityMeasure μU
  /-- the bid at round `t` from `u` and the past HOBs `m_1, …, m_{t−1}` -/
  bid : (t : Fin T) → U → (Fin t → ℝ) → ℝ
  measurable_bid : ∀ t : Fin T, Measurable (fun p : U × (Fin t → ℝ) => bid t p.1 p.2)
  bid_mem : ∀ (t : Fin T) (u : U) (h : Fin t → ℝ), bid t u h ∈ Set.Icc (0 : ℝ) 1

/-- The bid `b_t` realized by `π` at round `t` when its internal randomness is `u` and the HOB sequence
is `m`: the policy is fed `m_1, …, m_{t−1}` only. -/
def FullInfoPolicy.realizedBid {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U)
    (t : Fin T) (u : U) (m : Fin T → ℝ) : ℝ :=
  π.bid t u (fun s => m (Fin.castLE t.isLt.le s))

/-- The expected regret `E_G[R_T(π; v)]` with `v_t ≡ 1`: the regret (3) (`FirstPriceLearning.Adversarial.regret`) of the realized bids,
integrated over the policy's randomness `u ∼ μU` and the iid HOBs `m ∼ G^{⊗T}`, independent of `u`. -/
noncomputable def expectedRegret {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U)
    (μG : Measure ℝ) : ℝ :=
  ∫ p : U × (Fin T → ℝ),
      FirstPriceLearning.Adversarial.regret μG (fun _ => (1 : ℝ)) (fun t => π.realizedBid t p.1 p.2)
    ∂(π.μU.prod (Measure.pi fun _ : Fin T => μG))

end FirstPriceLearning.LowerBound


