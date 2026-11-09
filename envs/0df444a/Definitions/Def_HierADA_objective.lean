-- Prove2me | Definitions.Def_HierADA_objective
-- name    : HierADA_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:07.989128+00:00
-- url     : https://prove2.me/theorems/43132dbf-a1c3-4708-b892-22ccc70b752e
-- title:
--   Objective $\frac\tau4\langle G,w\rangle-R(w)$ of the weight update
-- statement:
--   For a threshold $\tau$, a block of $r$ samples, a score vector $G\in\mathbb R^r$ and weights $w\in\mathbb R^r$, the **objective** of the weight update is
--
--   $$
--   \frac\tau4\langle G,w\rangle-R(w)=\frac\tau4\sum_iG_iw_i-\frac r2\Big\|w-\frac{\mathbf 1}r\Big\|_2^2 .
--   $$
--
--   It is maximized over the capped simplex in Equation (2), and its maximum is the value function $\Phi$ of Equation (8).
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Equation (2), p.14, and Equation (8), p.20

import Mathlib
import Definitions.Def_HierADA_penalty

set_option autoImplicit false

namespace HierADA

/-- **The objective of the weight update** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data
Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03,
sha256 f220ae51…), Equation (2), p.14, and Equation (8), p.20: for threshold `τ`, block size `r`,
scores `G ∈ ℝ^r` and weights `w ∈ ℝ^r`,
$$\frac\tau4\langle G,w\rangle-R(w).$$ -/
noncomputable def objective (τ : ℝ) (r : ℕ) (G w : Fin r → ℝ) : ℝ :=
  τ / 4 * ∑ i, G i * w i - penalty r w

end HierADA


