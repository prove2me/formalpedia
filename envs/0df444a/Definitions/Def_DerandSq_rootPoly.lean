-- Prove2me | Definitions.Def_DerandSq_rootPoly
-- name    : DerandSq_rootPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:15.35573+00:00
-- url     : https://prove2.me/theorems/5d06e8f9-37c1-44b2-b66a-430aaafb2e1b
-- title:
--   The polynomial $(d-1)\chi\chi'' - (d-2)(\chi')^2$ of (4.4)
-- statement:
--   For a graph $H$ on $[d]$ with characteristic polynomial $\chi_x = \chi_x(H)$, let
--   $$
--   R_{d,H}(x) = (d - 1)\,\chi_x\,\chi''_x - (d - 2)\,(\chi'_x)^2,
--   $$
--   where $'$ is the derivative in $x$. The equation (4.4), $(d-1)\chi_x\chi''_x = (d-2)(\chi'_x)^2$, is $R_{d,H}(x) = 0$. For $d \geq 1$ the leading coefficient of $R_{d,H}$ is $d$; for $H = K_3$, $R_{3,K_3}(x) = 3(x - 3)(x + 1)^3$.
--
--   **Formalization Note** The coefficients $d - 1$ and $d - 2$ are real numbers (no natural-number subtraction).
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (4.4), p.19

import Mathlib
import Definitions.Def_DerandSq_chi

namespace DerandSq

open Polynomial in
/-- The polynomial `(d − 1)·χ_x(H)·χ''_x(H) − (d − 2)·χ'_x(H)²` whose largest real root is `x₀`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), (4.4), p.19). The coefficients `d − 1`, `d − 2` are real numbers. -/
noncomputable def rootPoly (d : ℕ) (H : SimpleGraph (Fin d)) : Polynomial ℝ :=
  C ((d : ℝ) - 1) * chi H * derivative (derivative (chi H)) -
    C ((d : ℝ) - 2) * (derivative (chi H)) ^ 2

end DerandSq


