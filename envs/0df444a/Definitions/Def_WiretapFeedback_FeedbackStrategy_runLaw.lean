-- Prove2me | Definitions.Def_WiretapFeedback_FeedbackStrategy_runLaw
-- name    : WiretapFeedback_FeedbackStrategy_runLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:55.46692+00:00
-- url     : https://prove2.me/theorems/22eb4f0e-8941-4bc7-81a1-5ec7f3da9509
-- title:
--   Joint law of a run of a strategy over a memoryless channel
-- statement:
--   Run a transmission–feedback strategy for $n$ rounds over a discrete memoryless channel $W:\mathcal X\to\mathcal O$: draw $U_x$ and $U_y$ independently from their laws; in round $s$ compute the input $X_s$ from $(U_x,U_y,O_0,\dots,O_{s-1})$ and draw $O_s\sim W(\cdot|X_s)$ independently of everything else given $X_s$. The result is the joint law of
--   $$
--   (U_x,U_y,O_0,\dots,O_{n-1}).
--   $$
--
--   Every other law of the paper (the law $P_{M\hat MZ^n\mathbf F}$ of a wiretap code, and the observation laws of an active hypothesis test) is an image of this one.
--
--   **Formalization Note** The law is built round by round with the monad operations of probability mass functions, so it is a probability distribution by construction.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, pp.1–2; §III, p.2

import Mathlib
import Definitions.Def_WildeQIT_Channel
import Definitions.Def_WiretapFeedback_finDistPMF
import Definitions.Def_WiretapFeedback_FeedbackStrategy_inputAt

namespace WiretapFeedback

/-- The joint law of `(Uₓ, U_y, O_0, …, O_{n−1})` when the transmission–feedback strategy `S`
is run for `n` rounds over the memoryless channel `W : X → O`
(Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §II, pp. 1–2, and §III, p. 2): `Uₓ ∼ lawX` and
`U_y ∼ lawY` independently, and in round `s` the output `O_s` is drawn from `W(·|X_s)`,
independently of everything else given the input `X_s = S.inputAt s Uₓ U_y (O_0, …, O_{s−1})`.

**Formalization Note** Built with `PMF.bind`/`PMF.map`, one round at a time (the auxiliary
`go ux uy k` is the law of the first `k` outputs given the local randomness), so that the law
is a probability mass function by construction. -/
noncomputable def FeedbackStrategy.runLaw {X O : Type} [Fintype O] {n : ℕ}
    (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O) :
    PMF (S.Ux × S.Uy × (Fin n → O)) :=
  S.lawX.bind fun ux => S.lawY.bind fun uy => (go ux uy n le_rfl).map fun o => (ux, uy, o)
where
  /-- The law of the first `k` channel outputs, given the local randomness. -/
  go (ux : S.Ux) (uy : S.Uy) : (k : ℕ) → k ≤ n → PMF (Fin k → O)
    | 0, _ => PMF.pure fun i => Fin.elim0 i
    | k + 1, h => (go ux uy k (Nat.le_of_succ_le h)).bind fun o =>
        (finDistPMF (W (S.inputAt ⟨k, h⟩ ux uy o))).map fun y => Fin.snoc (α := fun _ => O) o y

end WiretapFeedback


