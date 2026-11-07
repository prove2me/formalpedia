-- Prove2me | Definitions.Def_Max3CutHard_sumX
-- name    : Max3CutHard_sumX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:46.302579+00:00
-- url     : https://prove2.me/theorems/42798c73-f75a-415b-975c-3d1de6afad12
-- title:
--   $s(x)=x_1+x_2+x_3$
-- statement:
--   For $x\in\mathbb Z_3^3$,
--
--   $$s(x)=x_1+x_2+x_3\in\mathbb Z_3.$$
--
--   $s(x)=0$ exactly when the three colours are all equal or all distinct.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 3, p.5

import Mathlib

namespace Max3CutHard

/-- **`s(x) = x1 + x2 + x3 ∈ ℤ₃`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 3, p.5: "Write `s(x) = x1 + x2 + x3 ∈ ℤ₃`".
Tuples are 0-based. -/
def sumX (x : Fin 3 → ZMod 3) : ZMod 3 := x 0 + x 1 + x 2

end Max3CutHard


