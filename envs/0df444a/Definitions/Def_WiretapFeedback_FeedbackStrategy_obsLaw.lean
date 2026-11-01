-- Prove2me | Definitions.Def_WiretapFeedback_FeedbackStrategy_obsLaw
-- name    : WiretapFeedback_FeedbackStrategy_obsLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:42.557664+00:00
-- url     : https://prove2.me/theorems/4fd7e224-d0b2-495e-8761-75492f876dbf
-- title:
--   Observation law $(X^n,O^n,\mathbf F)$ of an active test
-- statement:
--   For a transmission–feedback strategy run over a channel $W$, the **observation** is the triple $(X^n,O^n,\mathbf F)$ of all channel inputs $X_0,\dots,X_{n-1}$, all channel outputs $O_0,\dots,O_{n-1}$ and all feedback $F_0,\dots,F_{n-1}$. This definition is its law, the image of the run law.
--
--   An active hypothesis test decides between $W$ and $V$ by applying a test to this observation ("a conditional distribution $T$ on $\{0,1\}$ given $X^n,Y^n,\mathbf F$").
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §III, p.2

import Mathlib
import Definitions.Def_WiretapFeedback_FeedbackStrategy_runLaw

namespace WiretapFeedback

/-- The law of what an active hypothesis test observes, `(Xⁿ, Oⁿ, 𝐅)`: the channel inputs
`X_0, …, X_{n−1}`, the channel outputs `O_0, …, O_{n−1}` and the feedback `F_0, …, F_{n−1}` of a
run of the strategy `S` over the channel `W` (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §III,
p. 2: "a conditional distribution `T` on `{0, 1}` given `Xⁿ, Yⁿ, 𝐅`"). -/
noncomputable def FeedbackStrategy.obsLaw {X O : Type} [Fintype O] {n : ℕ}
    (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O) :
    PMF ((Fin n → X) × (Fin n → O) × (Fin n → S.Fb)) :=
  (S.runLaw W).map fun r =>
    (fun s => S.inputAt s r.1 r.2.1 (fun i => r.2.2 ⟨i, lt_trans i.isLt s.isLt⟩),
     r.2.2,
     fun s => S.feedback s (fun i => r.2.2 ⟨i, lt_trans i.isLt s.isLt⟩) r.2.1)

end WiretapFeedback


