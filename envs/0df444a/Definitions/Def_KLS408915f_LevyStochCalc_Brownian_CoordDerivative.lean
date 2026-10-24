-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
-- name    : KLS408915f_LevyStochCalc_Brownian_CoordDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:19:51.575967+00:00
-- url     : https://prove2.me/theorems/ac6f7dcd-1b14-4230-85f8-7ba873c4a73d
-- title:
--   Coordinate partial derivatives from Fréchet derivatives
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For $x:\mathrm{Fin}\,n\to\mathbb R$ and coordinate indices $p,q$, `coordDeriv f' p x` evaluates the continuous linear map $f'(x)$ on the basis vector $e_p=\operatorname{Pi.single}(p,1)$, while `coordDeriv₂ f'' p q x` evaluates the second continuous multilinear term on $(e_p,e_q)$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L61-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, definition bundle `KLS408915f_LevyStochCalc_Brownian_CoordDerivative`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- The `p`-th partial derivative carried by a Fréchet derivative on `Fin n → ℝ`. -/
noncomputable def coordDeriv (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (p : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  f' x (Pi.single p 1)
/-- The `(p, q)` second partial derivative carried by a second Fréchet derivative on
`Fin n → ℝ`. -/
noncomputable def coordDeriv₂ (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (p q : Fin n) (x : Fin n → ℝ) : ℝ :=
  f'' x (Pi.single p 1) (Pi.single q 1)
end Coord
end LevyStochCalc


