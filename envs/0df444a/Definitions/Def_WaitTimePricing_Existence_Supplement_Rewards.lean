-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Supplement_Rewards
-- name    : WaitTimePricing_Existence_Supplement_Rewards
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:37:42.01464+00:00
-- url     : https://prove2.me/theorems/f574e6fc-e0ee-44c5-985f-ce23f76bc8c3
-- title:
--   Greatest-maximizer price feedback and abstract DDEs
-- statement:
--   For a reward $(v,\alpha)$ and a relative value function $V$, put
--   $$\xi(p,w)=v(p)-\alpha c(w)+V(w+t(p))-V(w).$$
--   Let $A(w)$ be its full argmax over $[0,\Gamma(w)]$, and set $\bar p(w)=\sup A(w)$. The feedback selects $\bar p(w)$ when $\xi(\bar p(w),w)\ge0$, and $U'(0)$ otherwise. States outside $[0,\bar w]$ reject without reading $\Gamma$ there. This preserves the greatest-price tie rule and admission at equality.
--
--   The abstract version of (12)–(15) uses the same service and threshold functions, with a supremum in its Hamiltonian and derivatives expressed by `HasDerivAt`. Attainment is not imposed by this definition: the concrete theorem concludes it, and the abstract counterexample explains why it need not hold. The objects are reusable for both objectives and for testing the stated general extension.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), pp. 12–13, (12)–(15), and pp. 17–18, (25)–(26)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Supplement_RewardInterface

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
noncomputable section
open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 18, (25)–(26); p. 12, (12)–(13).

The function ξ, pp. 17–18, (25), for a reward and relative value function.
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020).
Formalization Note: V is an explicit argument; concrete statements use the constructed Vbar. -/
def xi (M : Model) (R : Reward) (V : ℝ → ℝ) (p w : ℝ) : ℝ :=
  R.value p - R.weight * M.c w + V (w + tOf M p) - V w

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 18, (25)–(26); p. 12, (12)–(13).

The full set of price maximizers in (25), not an arbitrary selection. -/
def priceArgmax (M : Model) (R : Reward) (V : ℝ → ℝ) (w : ℝ) : Set ℝ :=
  {p ∈ Icc 0 (Gamma M w) | ∀ q ∈ Icc 0 (Gamma M w), xi M R V q w ≤ xi M R V p w}

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 18, (25)–(26); p. 12, (12)–(13).

The greatest maximizer pbar of (25), p. 18.
Formalization Note: `sSup` has a default on an empty set; attainment is a theorem conclusion. -/
def pbar (M : Model) (R : Reward) (V : ℝ → ℝ) (w : ℝ) : ℝ :=
  sSup (priceArgmax M R V w)

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 18, (25)–(26); p. 12, (12)–(13).

Feedback (26), p. 18. Formalization Note: equality ξ=0 admits. Above wbar it rejects
without consulting Gamma outside its domain. Negative states are unused and assigned rejection. -/
def feedback (M : Model) (R : Reward) (V : ℝ → ℝ) (w : ℝ) : ℝ :=
  if w ∈ Icc 0 (wbar M) then
    if 0 ≤ xi M R V (pbar M R V w) w then pbar M R V w else deriv M.U 0
  else deriv M.U 0

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 18, (25)–(26); p. 12, (12)–(13).

Abstract equations (12)–(15), pp. 12–13, without assuming a maximizer exists.
Formalization Note: the real sSup is meaningful only with boundedness; the counterexample
below shows why (V1),(V2) do not justify replacing a supremum by a maximum. -/
def abstractSolves (M : Model) (R : Reward) (g : ℝ) (V : ℝ → ℝ) : Prop :=
  (∀ w ∈ Ioc 0 (wbar M), HasDerivAt V
    (M.lam * max (sSup ((fun p => xi M R V p w) '' Icc 0 (Gamma M w))) 0 - g) w) ∧
  g = M.lam * max (sSup ((fun p => xi M R V p 0) '' Icc 0 (Gamma M 0))) 0 ∧
  (∀ w, wbar M < w → HasDerivAt V (-g) w) ∧ V (wbar M) = 0


end
end WaitTimePricing.Existence.Supplement


