-- Prove2me | Definitions.Def_RelaxRoundPoA_IsPayYourBid
-- name    : RelaxRoundPoA_IsPayYourBid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:51.474439+00:00
-- url     : https://prove2.me/theorems/a0a10a1e-49d6-46e0-923f-61b5be698667
-- title:
--   Pay-your-bid mechanism
-- statement:
--   A mechanism $M=(f,p)$ is **pay-your-bid** if every agent pays what it bid on the outcome it gets, $p_i(b)=b_i(f(b))$. In expectation: for every profile $b$ drawn from the weight classes and every agent $i$,
--
--   $$
--   \mathbf E\bigl[p_i(b)\bigr]=\mathbf E\bigl[b_i(f(b))\bigr].
--   $$
--
--   For a mechanism obtained by rounding, $f(b)$ is the rounded outcome, so each bidder is charged its declared value of the rounded outcome.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.6; §3, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Pay-your-bid mechanism.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.6: "in a pay-your-bid mechanism
`M = (f, p)`, `p_i(b) = b_i(f_i(b))`"; agents pay what they have bid on the outcome they get. In §3
(p.8) "each bidder is charged `b_i(x)`", `x` the (rounded) outcome.

`IsPayYourBid Val M` says that on every profile `b` drawn from the classes `Val`, agent `i`'s
expected payment is the expected value of its own bid at the outcome: `E[p_i(b)] = E[b_i(f(b))]`.

**Formalization Note** Only expected payments are recorded (agents are risk neutral, p.7). -/
def IsPayYourBid {N : Type*} {Ω' : Type*} [MeasurableSpace Ω'] (Val : N → Set (Ω' → ℝ≥0))
    (M : Mechanism N Ω') : Prop :=
  ∀ b, IsProfile Val b → ∀ i, M.expPay b i = ∫ x, (b i x : ℝ) ∂(M.outcome b)

end RelaxRoundPoA


