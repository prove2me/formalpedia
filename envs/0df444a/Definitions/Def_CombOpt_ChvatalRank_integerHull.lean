-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_integerHull
-- name    : CombOpt_ChvatalRank_integerHull
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:17.158024+00:00
-- url     : https://prove2.me/theorems/1f09ce40-cac4-4d9a-a2a6-fc70c3c4e391
-- title:
--   The integer hull $P_I$
-- statement:
--   For $P\subseteq\mathbb R^n$, the **integer hull** $P_I$ is the convex hull of the integral vectors in $P$:
--   $$
--   P_I=\operatorname{conv}\,(P\cap\mathbb Z^n).
--   $$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, p. 233 (PDF 241)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsIntegralVector

open Matrix

namespace CombOpt.ChvatalRank

/-- **Integer hull `P_I`.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, p. 233 (PDF 241): "P_I, the convex hull of the integral
vectors in P". -/
def integerHull {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  convexHull ℝ {x | x ∈ P ∧ IsIntegralVector x}

end CombOpt.ChvatalRank


