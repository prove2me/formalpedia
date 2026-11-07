-- Prove2me | Definitions.Def_IntroDelayAMDP_Coord
-- name    : IntroDelayAMDP_Coord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:01.034052+00:00
-- url     : https://prove2.me/theorems/49f6df11-04b9-426e-b1bf-ae074fb1d2bc
-- title:
--   Coordinates of the random tape
-- statement:
--   The tape has one coordinate for each of: the action draw $(\kappa,h)$ of episode $\kappa$ at layer $h$; the next-state draw $(\kappa,h)$; the acceptance coin $(k,s,a,\kappa)$ of the attempt of the estimate $(k,s,a)$ in episode $\kappa$; and the random-stop coin $(k,s,a,\kappa)$ of that attempt.
--
--   An estimate is keyed by $(k,s,a)$ because episode $k$ visits each layer once. Episodes are 0-based.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12; Algorithm 1, p.16

import Mathlib

namespace IntroDelayAMDP

/-- **Coordinates of the random tape** (the agent's internal randomness and the environment's
sampling, Section 2.1, printed p.12, and Algorithm 1, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).

The tape has one uniform `[0, 1]` coordinate for each of
1. `(κ, h)`: the action draw of episode `κ` at layer `h`;
2. `(κ, h)`: the next-state draw of episode `κ` after layer `h`;
3. `(k, s, a, κ)`: the acceptance coin of the attempt of the estimate `(k, s, a)` in episode `κ`
   (Algorithm 1, line 10);
4. `(k, s, a, κ)`: the random-stop coin of that attempt (line 12).

Episodes `κ, k` range over `Fin K` (0-based, the paper's `1, …, K`) and layers over `Fin H`.
An estimate is keyed by `(k, s, a)` because episode `k` visits each layer once. -/
abbrev Coord (St A : Type) (K H : ℕ) : Type :=
  (Fin K × Fin H) ⊕ (Fin K × Fin H) ⊕ (Fin K × St × A × Fin K) ⊕ (Fin K × St × A × Fin K)

end IntroDelayAMDP


