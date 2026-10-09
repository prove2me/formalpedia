-- Prove2me | Definitions.Def_ModernOnlineLearning_Aggregating_ShrunkSet
-- name    : ModernOnlineLearning_Aggregating_ShrunkSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:27.308081+00:00
-- url     : https://prove2.me/theorems/5ff64f4a-0fd8-42e2-90ef-604b45b1a620
-- title:
--   Proof of Theorem 11.5, p. 183 — shrunken competitor set
-- statement:
--   For a feasible set $V\subseteq\mathbb R^d$, a competitor $u\in V$, and a horizon $T$, the proof of Theorem 11.5 uses the translated, contracted set
--
--   $$V' = \left\{\frac{T/d}{T/d+1}u+\frac{1}{T/d+1}w:w\in V\right\}.$$
--
--   This is the region of the uniform prior used to compare the algorithm with the fixed point $u$.
--
--   **Formalization Note** The later theorems assume $d,T\geq1$, making both displayed ratios meaningful.
-- source:
--   Orabona, arXiv:1912.13213v10, proof of Theorem 11.5, p. 183

import Mathlib
set_option autoImplicit false

namespace ModernOnlineLearning.Aggregating

/-- The translated and contracted copy `V'` from the proof of Theorem 11.5. -/
def shrunkSet {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d)) (T : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  (fun w => (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) • u +
    (1 / ((T : ℝ) / (d : ℝ) + 1)) • w) '' V

end ModernOnlineLearning.Aggregating


