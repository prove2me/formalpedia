-- Prove2me | Definitions.Def_FoundationsRL_Structured_OracleGuarantee
-- name    : FoundationsRL_Structured_OracleGuarantee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:17:02.011996+00:00
-- url     : https://prove2.me/theorems/c7b00d99-2891-4fc8-b840-1ddf65a3ab02
-- title:
--   Definition 7 — Online regression oracle guarantee
-- statement:
--   This definition formalizes the guarantee an **online regression oracle** provides in the
--   structured bandit protocol (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, arXiv:2312.16730v1, Definition 7, p. 64). Over a horizon
--   $T$, at each round $t$ the oracle produces an estimate $\hat f_t : \Pi \to \mathbb{R}$ of
--   the ground-truth reward function $f^\star$, before the decision-maker plays $\pi_t \sim
--   p_t$. Definition 7 asserts that, with probability at least $1-\delta$,
--
--   $$
--   \sum_{t=1}^T \mathbb{E}_{\pi \sim p_t}\bigl[(\hat f_t(\pi) - f^\star(\pi))^2\bigr] \le \mathrm{EstSq}(F, T, \delta).
--   $$
--
--   `OracleGuarantee T fhat fstar p EstSq` packages exactly this bound as a `Prop` on a
--   realized run.
--
--   **Formalization Note** As in the earlier bandit missions of this series, the
--   probability-$1-\delta$ qualifier of the source is captured here as an explicit hypothesis
--   on the realized run (the quantity itself, conditional on the event holding), rather than
--   as a statement quantified over the randomness that produces $\hat f$ and $p$ — every
--   result in this chapter that uses this guarantee is a purely algebraic consequence of the
--   bound once it holds.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 7, p. 64

import Mathlib

namespace FoundationsRL.Structured

/-- The guarantee provided by an online regression oracle for the structured bandit protocol
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Definition 7, p. 64). Given a horizon `T`, a sequence of oracle estimates
`fhat : Fin T → (S → ℝ)`, the ground-truth reward function `fstar`, and the decision-maker's
realized randomization `p : Fin T → (S → ℝ)` at each round (`p t` a probability vector over the
decision space `Π`), `OracleGuarantee T fhat fstar p EstSq` packages the event

`∑_{t=1}^T E_{π_t ∼ p_t}[(f̂_t(π_t) − f⋆(π_t))²] ≤ EstSq(F, T, δ)`

that Definition 7 asserts holds with probability at least `1 − δ`. As in the earlier contextual
bandit mission, the probability-`1 − δ` event of the source is captured here as an explicit
hypothesis on the realized run, rather than as a statement quantified over the randomness that
produces `f̂` and `p`. -/
def OracleGuarantee {S : Type*} [Fintype S] (T : ℕ) (fhat : Fin T → S → ℝ) (fstar : S → ℝ)
    (p : Fin T → S → ℝ) (EstSq : ℝ) : Prop :=
  ∑ t : Fin T, ∑ π : S, p t π * (fhat t π - fstar π) ^ 2 ≤ EstSq

end FoundationsRL.Structured


