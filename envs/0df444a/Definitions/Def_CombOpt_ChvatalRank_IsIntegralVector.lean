-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsIntegralVector
-- name    : CombOpt_ChvatalRank_IsIntegralVector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:22.841084+00:00
-- url     : https://prove2.me/theorems/011dfa19-dc7e-47a4-a9aa-9244abfee389
-- title:
--   Integral vector
-- statement:
--   A vector $x\in\mathbb R^n$ is **integral** if every component $x_i$ is an integer.
--
--   This is the sense of "integral" in the coefficient vectors of cuts, in the integral vectors of a polyhedron and in the integer hull.
--
--   **Formalization Note** It is a predicate on `Fin n → ℝ`, so that integral coefficient vectors and points of $\mathbb R^n$ need no casts.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, pp. 229–233 (PDF 237–241)

import Mathlib

open Matrix

namespace CombOpt.ChvatalRank

/-- **Integral vector.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), used throughout §6.7: every component is an integer.

**Formalization Note.** A predicate on real vectors, so that cut coefficients and points of `ℝⁿ` need
no casts. `P_I`, `w integral` and `c integral` all use it. -/
def IsIntegralVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, ∃ k : ℤ, x i = k

end CombOpt.ChvatalRank


