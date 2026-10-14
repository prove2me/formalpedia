-- Prove2me | Definitions.Def_FirstPriceLearning_Stochastic_Policy
-- name    : FirstPriceLearning_Stochastic_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:49.609468+00:00
-- url     : https://prove2.me/theorems/729a9c45-570a-48c1-ada2-25c9ce969b0a
-- title:
--   §2.2, p. 9 — non-anticipating randomized bidding policies with censored feedback max{b_t, m_t}, and their expected regret
-- statement:
--   A **bidding policy** for $T$ rounds owns an internal randomness $u$ with a probability law $\mu_U$. In round $t$ it bids
--
--   $$
--   b_t=\pi_t\big(u;\ v_1,\dots,v_t;\ y_1,\dots,y_{t-1}\big)\in[0,1],\qquad y_s=\max\{b_s,m_s\},
--   $$
--
--   i.e. the bid depends only on the internal randomness, the private values seen so far, and the **censored feedback** of the earlier rounds: only the winning bid $\max\{b_s,m_s\}$ is revealed, which tells the bidder whether she won ($y_s=b_s$) and the HOB $m_s$ only if she lost. The policy cannot see the HOBs themselves, their distribution $G$, or the value distribution $F$.
--
--   Running a policy on values $v$ and HOBs $m$ produces the bids recursively. When $v_1,\dots,v_T$ are iid $F$, $m_1,\dots,m_T$ are iid $G$, and $u$, $v$, $m$ are independent, the **expected regret** is
--
--   $$
--   \mathbb E[R_T(\pi;v)]=\int R_T(\pi;v)\ d\big(\mu_U\otimes F^{\otimes T}\otimes G^{\otimes T}\big)(u,v,m),
--   $$
--
--   with $R_T$ the regret (3); the expectation is joint over $v$ and the randomness of the auction and the policy, as in §2.2.
--
--   **Formalization Note.** Non-anticipation is enforced by the argument types: the round-$t$ bid map takes `Fin (t+1) → ℝ` (values) and `Fin t → ℝ` (feedback). No measurability is bundled into a policy; every theorem that bounds an expected regret asserts that the regret is integrable, so the integral is a genuine expectation and not Lean's default value $0$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 9, §2.2 (feedback model, (3) and the expected regret)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- A non-anticipating randomized bidding policy for `T` rounds of first-price auctions with
censored feedback (§2.2, p. 9). The policy owns an internal-randomness space `(U, μU)`. At round
`t` (paper round `t.val + 1`) its bid is a function of the internal randomness `u`, the values
`v_1, …, v_t` seen so far (`Fin (t+1) → ℝ`) and the feedback `y_1, …, y_{t-1}` of the earlier
rounds (`Fin t → ℝ`), where `y_s = max {b_s, m_s}` is the winning bid. It cannot read the
highest other bids, their law `G`, or the value law `F`. Bids lie in `[0, 1]`. -/
structure Policy (T : ℕ) where
  /-- The internal-randomness space. -/
  U : Type
  [mU : MeasurableSpace U]
  /-- The law of the internal randomness. -/
  μU : Measure U
  [prob : IsProbabilityMeasure μU]
  /-- The bid at round `t` from `(u, v_1..v_t, y_1..y_{t-1})`. -/
  bid : (t : Fin T) → U → (Fin (t.val + 1) → ℝ) → (Fin t.val → ℝ) → ℝ
  bid_mem : ∀ t u vs ys, bid t u vs ys ∈ Set.Icc (0 : ℝ) 1

attribute [instance] Policy.mU Policy.prob

namespace Policy

variable {T : ℕ}

/-- The censored feedback `y_s = max {b_s, m_s}` of the first `n` rounds, produced by running
the policy `π` with internal randomness `u` on values `v` and highest other bids `m`. Rounds
`n ≥ T` do not occur and carry `0`. -/
noncomputable def feedback (π : Policy T) (u : π.U) (v m : Fin T → ℝ) : (n : ℕ) → (Fin n → ℝ)
  | 0 => Fin.elim0
  | n + 1 =>
    Fin.snoc (α := fun _ => ℝ) (feedback π u v m n)
      (if h : n < T then
        max (π.bid ⟨n, h⟩ u (fun i => v ⟨i.val, by have := i.isLt; omega⟩) (feedback π u v m n))
          (m ⟨n, h⟩)
      else 0)

/-- The realized bid `b_t` of `π` at round `t`. -/
noncomputable def bids (π : Policy T) (u : π.U) (v m : Fin T → ℝ) (t : Fin T) : ℝ :=
  π.bid t u (fun i => v ⟨i.val, by have := i.isLt; have := t.isLt; omega⟩) (π.feedback u v m t.val)

/-- The joint law of `(u, v, m)` when the values are iid `F` and the highest other bids are iid
`G` (law `μG`), all three independent: `μU ⊗ F^{⊗T} ⊗ G^{⊗T}`. -/
noncomputable def jointLaw (π : Policy T) (F μG : Measure ℝ) :
    Measure (π.U × (Fin T → ℝ) × (Fin T → ℝ)) :=
  π.μU.prod ((Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG))

/-- The regret (3) of `π` as a function of the randomness `(u, v, m)`. -/
noncomputable def regretOf (π : Policy T) (μG : Measure ℝ) (ω : π.U × (Fin T → ℝ) × (Fin T → ℝ)) :
    ℝ :=
  regret μG ω.2.1 (π.bids ω.1 ω.2.1 ω.2.2)

/-- The expected regret `𝔼[R_T(π; v)]`, jointly over the values, the highest other bids and the
policy's internal randomness. -/
noncomputable def expectedRegret (π : Policy T) (F μG : Measure ℝ) : ℝ :=
  ∫ ω, π.regretOf μG ω ∂(π.jointLaw F μG)

end Policy

end FirstPriceLearning.Stochastic


