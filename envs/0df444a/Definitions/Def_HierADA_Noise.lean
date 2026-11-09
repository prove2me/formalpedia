-- Prove2me | Definitions.Def_HierADA_Noise
-- name    : HierADA_Noise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:26.837303+00:00
-- url     : https://prove2.me/theorems/b9ead383-f429-4de9-a7c7-baafb74bc6fe
-- title:
--   Noise realization $(E_t, Z_{j,\varphi}, V_m)$
-- statement:
--   A **noise realization** is a triple $z=(E,Z,V)$ of real sequences: $E_t$ is the noise added to the answer of query $t$ (Algorithm 1, line 5); $Z_{j,\varphi}$ is the threshold noise of edge $j$ in its phase $\varphi$, where phase $\varphi$ starts after the $\varphi$-th correction on that edge (Algorithm 2, line 8); and $V_m$ is the noise of the $m$-th signed test of the private comparison overall.
--
--   Assigning all draws in advance in this way is the device of the proof of Theorem 3.7. All indices start at $0$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Algorithms 1–2, pp.13–14, and the proof of Theorem 3.7, p.25

import Mathlib

set_option autoImplicit false

namespace HierADA

/-- **A realization of the mechanism's noise** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive
Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of
2026-11-03, sha256 f220ae51…), Algorithms 1–2, pp.13–14, and the proof of Theorem 3.7, p.25
("assign independent randomness to all potential phases and numerical releases in advance").

A triple `z = (E, Z, V)`: `E t` is the answer noise of query `t` (Algorithm 1, line 5), `Z j φ` the
threshold noise of edge `j` in its phase `φ` (Algorithm 2; phase `φ` starts after the `φ`-th
correction on that edge), and `V m` the noise of the `m`-th signed test of `Compare` overall.
All indices are 0-based. -/
abbrev Noise : Type := (ℕ → ℝ) × (ℕ → ℕ → ℝ) × (ℕ → ℝ)

end HierADA


