-- Prove2me | Definitions.Def_WiretapFeedback_WiretapCode_toStrategy
-- name    : WiretapFeedback_WiretapCode_toStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:33.130678+00:00
-- url     : https://prove2.me/theorems/90cc21c5-d1ef-4371-8622-c6e381c613bb
-- title:
--   A wiretap code as a transmission–feedback strategy
-- statement:
--   A wiretap code used with a message $M\sim\mu$ is a transmission–feedback strategy over the channel $\mathcal X\to\mathcal Y\times\mathcal Z$: the transmitter's local randomness is the pair $(M,U_x)\sim\mu\otimes P_{U_x}$, the receiver's is $U_y$, and the feedback reads only the $\mathcal Y$-components of the channel outputs.
--
--   This is the observation behind the proof of Theorem 6: a test on the code's laws together with the code constitutes an active hypothesis test.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, pp.1–2; proof of Theorem 6, p.4

import Mathlib
import Definitions.Def_WiretapFeedback_WiretapCode
import Definitions.Def_WiretapFeedback_FeedbackStrategy

namespace WiretapFeedback

/-- A wiretap code, with the message `M ∼ μ`, viewed as a transmission–feedback strategy over the
channel `X → Y × Z`: the transmitter's randomness is the pair `(M, Uₓ) ∼ μ ⊗ lawX`, and the
feedback reads only the `Y`-components of the outputs (Hayashi–Tyagi–Watanabe,
arXiv:1410.0443v1, §II, pp. 1–2). This is the observation in the proof of Theorem 6 (p. 4) that
"a test … along with the wiretap code constitutes an active hypothesis test". -/
noncomputable def WiretapCode.toStrategy {X Y : Type} (Z : Type) {N n : ℕ}
    (c : WiretapCode X Y N n) (μ : PMF (Fin N)) : FeedbackStrategy X (Y × Z) n where
  Fb := c.Fb
  Ux := Fin N × c.Ux
  Uy := c.Uy
  lawX := μ.bind fun m => c.lawX.map fun u => (m, u)
  lawY := c.lawY
  feedback s o uy := c.feedback s (fun i => (o i).1) uy
  encoder s a f := c.encoder s a.1 a.2 f

end WiretapFeedback


