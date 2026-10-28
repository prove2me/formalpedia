-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
-- name    : KLSModular_LevyStochCalc_Brownian_CoordDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:56:20.473243+00:00
-- url     : https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d
-- title:
--   Coordinate partial derivatives from Fréchet derivatives
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For $x:\mathrm{Fin}\,n\to\mathbb R$ and coordinate indices $p,q$, `coordDeriv f' p x` evaluates the continuous linear map $f'(x)$ on the basis vector $e_p=\operatorname{Pi.single}(p,1)$, while `coordDeriv₂ f'' p q x` evaluates the second continuous multilinear term on $(e_p,e_q)$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.TaylorTwoVector
--   import Mathlib.Analysis.Calculus.MeanValue
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def coordDeriv (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (p : Fin n)
--       (x : Fin n → ℝ) : ℝ :=
--     f' x (Pi.single p 1)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/TaylorTwoVector`](https://prove2.me/theorems/7b95962e-e11d-4fe9-a26b-01c2fa7c2715).
--
--   Theorems in source order:
--
--   - [`norm_le_sum_abs_apply`](https://prove2.me/theorems/08f4df99-b546-4459-b36d-34b026059891)
--   - [`norm_le_sum_abs_apply₂`](https://prove2.me/theorems/9c1c40e0-fc30-43e7-954a-44660a6d0cf5)
--   - [`abs_coordDeriv₂_sub_le_affine`](https://prove2.me/theorems/03b14996-130d-4e19-92fe-54bf2136b9a7)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CoordDerivative.lean) · `LevyStochCalc.Brownian.CoordDerivative` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L61-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, definition bundle `KLSModular_LevyStochCalc_Brownian_CoordDerivative`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoVector
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


