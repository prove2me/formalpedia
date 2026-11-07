-- Prove2me | Definitions.Def_IntroDelayAMDP_Tape
-- name    : IntroDelayAMDP_Tape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:50.463035+00:00
-- url     : https://prove2.me/theorems/8315dbed-0a85-4e41-ba47-3a0dcaedaa9a
-- title:
--   The random tape
-- statement:
--   A sample point assigns a number in $[0,1]$ to every coordinate of the tape.
--
--   **Formalization Note** The tape is one realization of the protocol: Algorithm 1 is a function of the tape, and the tape carries the product of uniform laws. Every quantity in the theorems depends only on the joint law of the run, which is the paper's.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12

import Mathlib
import Definitions.Def_IntroDelayAMDP_Coord

namespace IntroDelayAMDP

/-- **The random tape** (Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, printed p.12: "`F_k` contains the history of
episodes `1, 2, …, k`, including the agent's internal randomness"). A sample point `ω` assigns a
number in the unit interval to every coordinate of `Coord St A K H`.

**Formalization Note.** The tape is one realization of the protocol: Algorithm 1 is a function of
the tape (`runState`), and the tape carries the product of uniform laws (`tapeMeasure`). Every
quantity in the theorems depends only on the joint law of the run, which is the paper's. -/
abbrev Tape (St A : Type) (K H : ℕ) : Type := Coord St A K H → unitInterval

end IntroDelayAMDP


