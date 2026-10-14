-- Prove2me | Definitions.Def_FirstPriceLearning_NonIID_ThresholdModel
-- name    : FirstPriceLearning_NonIID_ThresholdModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:25.46286+00:00
-- url     : https://prove2.me/theorems/e7d1833b-bf23-46cb-8550-1779266a8063
-- title:
--   §5.2, p. 33 — threshold HOB model, full-information randomized policies and the expected regret
-- statement:
--   This module formalizes the non-iid model of §5.2 of Han, Zhou and Weissman.
--
--   Fix a horizon $T$, two probability laws $P,Q$ on $\mathbb R$ and a threshold $v^\star$. At round $t\in[T]$ the bidder sees a private value $v_t$, bids $b_t\in[0,1]$, and the highest other bid is drawn as
--   $$
--   m_t\sim P\ \text{ if } v_t<v^\star,\qquad m_t\sim Q\ \text{ if } v_t\ge v^\star,
--   $$
--   independently across rounds. Feedback is **full information**: $m_t$ is revealed at the end of round $t$.
--
--   A **policy** draws internal randomness $u$ from a probability space $(U,\mu_U)$ once; its bid at round $t$ is a measurable function
--   $$
--   b_t=\pi_t\big(u;\,v_1,\dots,v_t;\,m_1,\dots,m_{t-1}\big)\in[0,1].
--   $$
--   For an oblivious (fixed) value sequence $v=(v_1,\dots,v_T)$, the **expected regret** is
--   $$
--   \sum_{t=1}^T\Big(\max_{b\in[0,1]}\mathbb E_{m\sim L_t}\big[(v_t-b)\mathbb 1(b\ge m)\big]-\mathbb E\big[(v_t-b_t)\mathbb 1(b_t\ge m_t)\big]\Big),\qquad L_t=\begin{cases}P,&v_t<v^\star,\\ Q,&v_t\ge v^\star,\end{cases}
--   $$
--   where the second expectation is over $u\sim\mu_U$ and the independent $m_1,\dots,m_T$. The oracle knows $v^\star$ and bids optimally at every round; this is the paper's regret display on p. 33.
--
--   **Formalization Note** Rounds are `Fin T`; Lean round $t$ is the paper's round $t+1$. The paper's two-term sum $\mathbb 1(v_t<v^\star)\mathbb E_P[\cdot]+\mathbb 1(v_t\ge v^\star)\mathbb E_Q[\cdot]$ is written with the law $L_t$, and the oracle term as $\sup_{b\in[0,1]}R(v_t,b)$ (no arg max is chosen). The laws $P,Q$ are not inputs of the policy; Theorem 8 fixes them before the policy is chosen, which is how "revealed to the bidder" enters.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 33, §5.2 (the threshold model and its regret display)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

namespace FirstPriceLearning.NonIID

open MeasureTheory

/-- The thresholded law of the highest other bid (arXiv:2003.09795v7, p. 33): `m_t ∼ P` if `v_t < v⋆`
and `m_t ∼ Q` if `v_t ≥ v⋆`. -/
noncomputable def hobLaw (P Q : Measure ℝ) (vstar v : ℝ) : Measure ℝ :=
  if v < vstar then P else Q

/-- A randomized, non-anticipating bidding policy with full-information feedback over the horizon `T`
(p. 33). Round `t : Fin T` is the paper's round `t.val + 1`. The policy draws its internal randomness
`u ∈ U` from the probability measure `μU` once; its bid at round `t` is a measurable function of `u`,
of the private values `v_1, …, v_t` seen so far (`Fin (t.val + 1) → ℝ`) and of the past highest
other bids `m_1, …, m_{t−1}` (`Fin t.val → ℝ`), and lies in `[0, 1]`. -/
structure FullInfoPolicy (T : ℕ) where
  /-- The space of the policy's internal randomness. -/
  U : Type
  /-- Its σ-algebra. -/
  instU : MeasurableSpace U
  /-- The law of the internal randomness. -/
  μU : Measure U
  /-- The internal randomness is drawn from a probability measure. -/
  isProb : IsProbabilityMeasure μU
  /-- `bid t u (v_1, …, v_t) (m_1, …, m_{t−1})` is the bid `b_t`. -/
  bid : (t : Fin T) → U → (Fin (t.val + 1) → ℝ) → (Fin t.val → ℝ) → ℝ
  /-- Each bid is jointly measurable in the randomness and the observed history. -/
  measurable_bid : ∀ t : Fin T,
    Measurable (fun p : U × (Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ) => bid t p.1 p.2.1 p.2.2)
  /-- Bids lie in `[0, 1]` (p. 8). -/
  bid_mem : ∀ (t : Fin T) (u : U) (vs : Fin (t.val + 1) → ℝ) (ms : Fin t.val → ℝ),
    bid t u vs ms ∈ Set.Icc (0 : ℝ) 1

attribute [instance] FullInfoPolicy.instU FullInfoPolicy.isProb

/-- The bid `b_t` that policy `π` places at round `t` against the value sequence `v`, given its
internal randomness `u` and the highest other bids `m` (only `m_1, …, m_{t−1}` are read). -/
noncomputable def FullInfoPolicy.bidAt {T : ℕ} (π : FullInfoPolicy T) (v : Fin T → ℝ) (t : Fin T)
    (u : π.U) (m : Fin T → ℝ) : ℝ :=
  π.bid t u (fun s => v ⟨s.val, by omega⟩) (fun s => m ⟨s.val, by omega⟩)

/-- The law of the highest other bids `(m_1, …, m_T)` in the threshold model: independent across
rounds, `m_t ∼ P` if `v_t < v⋆` and `m_t ∼ Q` otherwise (p. 33). -/
noncomputable def hobSeqLaw {T : ℕ} (P Q : Measure ℝ) (vstar : ℝ) (v : Fin T → ℝ) :
    Measure (Fin T → ℝ) :=
  Measure.pi (fun t => hobLaw P Q vstar (v t))

/-- The expected regret of policy `π` in the threshold model of p. 33, against the oblivious value
sequence `v` and threshold `v⋆`:
`∑_t ( max_{b ∈ [0,1]} E_{m ∼ L_t}[(v_t − b) 𝟙(b ≥ m)] − E[(v_t − b_t) 𝟙(b_t ≥ m_t)] )`
where `L_t = P` if `v_t < v⋆` and `L_t = Q` otherwise, and the second expectation is over the
policy's internal randomness and the independent highest other bids. -/
noncomputable def expectedRegret {T : ℕ} (π : FullInfoPolicy T) (P Q : Measure ℝ) (vstar : ℝ)
    (v : Fin T → ℝ) : ℝ :=
  ∑ t : Fin T,
    (FirstPriceLearning.Stochastic.oracle (hobLaw P Q vstar (v t)) (v t) -
      ∫ p : π.U × (Fin T → ℝ), FirstPriceLearning.Stochastic.payoff (v t) (π.bidAt v t p.1 p.2) (p.2 t)
        ∂(π.μU.prod (hobSeqLaw P Q vstar v)))

end FirstPriceLearning.NonIID


