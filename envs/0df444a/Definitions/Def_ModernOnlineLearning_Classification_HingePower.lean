-- Prove2me | Definitions.Def_ModernOnlineLearning_Classification_HingePower
-- name    : ModernOnlineLearning_Classification_HingePower
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:08.747135+00:00
-- url     : https://prove2.me/theorems/76bfbae1-e3d8-47a7-9a6c-66290c40daee
-- title:
--   p. 143 — real powers of the binary hinge loss
-- statement:
--   For a real score $m$, label $y$, and power $q$, the hinge-power loss is
--
--   $$
--   \ell_q(m,y)=\max(1-ym,0)^q.
--   $$
--
--   This is the convex classification surrogate used to measure a fixed competitor in Chapter 8. It is independent of the Perceptron update rule.
--
--   **Formalization Note** The definition is total on real inputs; the theorems using it require $y\in\{-1,1\}$ and $q\ge1$. The base is nonnegative, so a zero hinge value has the intended real-power value.
-- source:
--   Orabona, arXiv:1912.13213v10, hinge-power loss, p. 143

import Mathlib

namespace ModernOnlineLearning.Classification

/-- The power hinge loss `ℓ_q(m,y) = max(1 - ym,0)^q`, p. 143. -/
noncomputable def hingePower (q m y : ℝ) : ℝ :=
  (max (1 - y * m) 0) ^ q

end ModernOnlineLearning.Classification


