-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
-- name    : KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:19:37.738555+00:00
-- url     : https://prove2.me/theorems/83e64f22-edd0-4680-b39d-cb724c622f73
-- title:
--   Second-order Taylor remainder along a sequence
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a real-valued function $f$ on a real normed space $E$, first derivative $f':E\to E\toL[\mathbb R]\mathbb R$, second derivative $f'':E\to E\toL[\mathbb R]E\toL[\mathbb R]\mathbb R$, sequence $x_i$, and $m\in\mathbb N$, `taylorRemainderNormed` is $f(x_m)-f(x_0)$ minus the sum of the first-order increments and the quadratic terms divided by $2$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoVector.lean#L73-L79 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoVector`, definition bundle `KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoVector.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The second-order Taylor remainder of `f` along the first `m` steps of the sequence `x` in a
normed space. -/
noncomputable def taylorRemainderNormed (f : E → ℝ) (f' : E → E →L[ℝ] ℝ)
    (f'' : E → E →L[ℝ] E →L[ℝ] ℝ) (x : ℕ → E) (m : ℕ) : ℝ :=
  f (x m) - f (x 0)
    - ((∑ i ∈ Finset.range m, f' (x i) (x (i + 1) - x i))
      + ∑ i ∈ Finset.range m, f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2)
end LevyStochCalc


