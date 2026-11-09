-- Prove2me | Definitions.Def_HierADA_RandMechanism
-- name    : HierADA_RandMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:22.507354+00:00
-- url     : https://prove2.me/theorems/46c53855-5e91-47e8-970d-47f598b3d78e
-- title:
--   Randomized ADA mechanism on $N$ samples
-- statement:
--   A **randomized mechanism** on $N$ samples over a domain $X$ is a family $(M_\omega)_{\omega\in\Omega}$ of deterministic mechanisms indexed by a seed. Given the seed $\omega$, the ordered sample $s=(s_1,\dots,s_N)\in X^N$, the history of earlier (query, answer) pairs and the current statistical query $f:X\to[0,1]$, the mechanism returns the real answer $M_\omega(s,\text{history},f)$.
--
--   The seed is drawn once from a probability measure on $\Omega$ chosen together with the mechanism. Randomness drawn during the interaction, as in the paper's Algorithms 1–2, is covered by assigning all draws in advance. The mechanism never sees the distribution of the samples.
--
--   **Formalization Note** The deterministic mechanisms are the published `IsRandomnessNecessaryADA.Plain.Mechanism X N`.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 1, p.3, and Theorem 3.8, p.25

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol

set_option autoImplicit false

namespace HierADA

/-- **Randomized ADA mechanism on `N` samples** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Section 1.1, p.3 (the ADA setting) and Theorem 3.8,
p.25 ("there exists a randomized mechanism").

A randomized mechanism is a family, indexed by a seed `ω : Ω`, of deterministic mechanisms in the
sense of the published `IsRandomnessNecessaryADA.Plain.Mechanism X N`: given the ordered sample
`s : Fin N → X`, the history of past (query, answer) pairs and the current statistical query, it
returns a real answer.

**Formalization Note.** The seed is drawn once, from a probability measure on `Ω` chosen together
with the mechanism, and every answer is a deterministic function of (seed, sample, history,
current query). This covers mechanisms that draw fresh randomness at every round: all such draws
can be assigned in advance ("assign independent randomness to all potential phases and numerical
releases in advance", p.25). The mechanism never sees the distribution. -/
abbrev RandMechanism (Ω X : Type) (N : ℕ) : Type :=
  Ω → IsRandomnessNecessaryADA.Plain.Mechanism X N

end HierADA


