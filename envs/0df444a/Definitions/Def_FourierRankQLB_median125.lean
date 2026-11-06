-- Prove2me | Definitions.Def_FourierRankQLB_median125
-- name    : FourierRankQLB_median125
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:16.756708+00:00
-- url     : https://prove2.me/theorems/f10cb5d2-c8f2-4926-8e2c-d341b8c2208e
-- title:
--   The median of 125 real numbers
-- statement:
--   For real numbers $z_1,\dots,z_{125}$, their median: the 63rd smallest. It is step (3) of the determinant predictor.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.4, step (3), p.29

import Mathlib

namespace FourierRankQLB

/-- The median of `125` real numbers: the `63`rd order statistic.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.4, step (3), p. 29.

**Formalization Note.** `Tuple.sort z` sorts `z` increasingly, and the index `62` is the `63`rd
position counted from one. -/
noncomputable def median125 (z : Fin 125 → ℝ) : ℝ := z (Tuple.sort z ⟨62, by norm_num⟩)

end FourierRankQLB


