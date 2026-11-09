-- Prove2me | Definitions.Def_HierADA_penalty
-- name    : HierADA_penalty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:14.94811+00:00
-- url     : https://prove2.me/theorems/8b54dfe1-d697-4dce-886b-700d63258702
-- title:
--   Quadratic penalty $R(w)=\frac r2\sum_i(w_i-1/r)^2$
-- statement:
--   For a block of $r$ samples and weights $w\in\mathbb R^r$, the **penalty** is
--
--   $$
--   R(w)=\frac r2\sum_{i=1}^r\Big(w_i-\frac1r\Big)^2=\frac r2\Big\|w-\frac{\mathbf 1}r\Big\|_2^2 .
--   $$
--
--   It measures the distance from the uniform weights and vanishes exactly at them (for $r\ge1$).
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Lemma 3.1, p.14, and Equation (2), p.14

import Mathlib

set_option autoImplicit false

namespace HierADA

/-- **The quadratic penalty `R`** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data Analysis
and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03, sha256
f220ae51…), Lemma 3.1, p.14, and Equation (2), p.14:
$$R(w)=\frac r2\sum_{i=1}^r\Bigl(w_i-\frac1r\Bigr)^2=\frac r2\Bigl\|w-\frac{\mathbf 1}r\Bigr\|_2^2 .$$ -/
noncomputable def penalty (r : ℕ) (w : Fin r → ℝ) : ℝ :=
  (r : ℝ) / 2 * ∑ i, (w i - 1 / (r : ℝ)) ^ 2

end HierADA


