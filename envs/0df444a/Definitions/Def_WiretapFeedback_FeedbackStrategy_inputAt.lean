-- Prove2me | Definitions.Def_WiretapFeedback_FeedbackStrategy_inputAt
-- name    : WiretapFeedback_FeedbackStrategy_inputAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:35.596819+00:00
-- url     : https://prove2.me/theorems/7b0661cc-bf5b-4f9a-8b55-7b9bc2374e40
-- title:
--   Channel input of round $s$ of a strategy
-- statement:
--   For a transmission–feedback strategy, local randomness $(u_x,u_y)$ and channel outputs $o_0,\dots,o_{s-1}$ of the first $s$ rounds, the channel input of round $s$ is
--   $$
--   X_s=e_s\bigl(u_x,F_0,\dots,F_s\bigr),\qquad F_r=f_r(o_0,\dots,o_{r-1},u_y)\quad(0\le r\le s).
--   $$
--
--   It is the deterministic part of one round of the protocol; the random part is the channel output drawn from $W(\cdot|X_s)$.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, pp.1–2; §III, p.2

import Mathlib
import Definitions.Def_WiretapFeedback_FeedbackStrategy

namespace WiretapFeedback

/-- The channel input of round `s` of a transmission–feedback strategy, as a function of the local
randomness `(Uₓ, U_y)` and of the channel outputs `O_0, …, O_{s−1}` observed so far:
`X_s = e_s(Uₓ, F_0, …, F_s)` with `F_r = f_r(O_0, …, O_{r−1}, U_y)` for `r ≤ s`
(Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §II, pp. 1–2, and §III, p. 2). -/
def FeedbackStrategy.inputAt {X O : Type} {n : ℕ} (S : FeedbackStrategy X O n) (s : Fin n)
    (ux : S.Ux) (uy : S.Uy) (o : Fin s → O) : X :=
  S.encoder s ux fun r =>
    S.feedback ⟨r, Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp r.isLt) s.isLt⟩
      (fun i => o ⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.lt_succ_iff.mp r.isLt)⟩) uy

end WiretapFeedback


