-- Prove2me | Definitions.Def_RPB108_ThreeGram
-- name    : RPB108_ThreeGram
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-11T03:56:51.684927+00:00
-- url     : https://prove2.me/theorems/85530767-fddd-4eb8-b54f-18d8f123031b
-- title:
--   RPB108 three-coordinate Gram functions
-- statement:
--   Defines the three-coordinate off-diagonal weights, row margins, real Gram form and complex Gram form. The complex form is the sum of real matrix entries times the real part of conjugate coordinate products. All data are exact. Original matrices satisfying these intervals are supplied separately; no realization attachment is proved by these definitions.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/ThreeGram.lean#L7-L14; source SHA256 a442815ca3343f4cfad3b84e0834871dd329630111b0d35a9d569431a00eb5d8. Native definitions preserved verbatim by compiler-derived skeleton subtraction.

import Mathlib

open scoped BigOperators
namespace WeilDefect.RPB108

noncomputable def offWeights (u : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0,u 0,u 1], ![u 0,0,u 2], ![u 1,u 2,0]]
noncomputable def rowMargins (d u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![d 0-u 0-u 1, d 1-u 0-u 2, d 2-u 1-u 2]
noncomputable def realGram (A : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j*x i*x j
noncomputable def complexGram (A : Fin 3 → Fin 3 → ℝ) (z : Fin 3 → ℂ) : ℝ :=
  ∑ i, ∑ j, A i j*(star (z i)*z j).re











end WeilDefect.RPB108


