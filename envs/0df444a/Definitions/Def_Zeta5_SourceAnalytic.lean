-- Prove2me | Definitions.Def_Zeta5_SourceAnalytic
-- name    : Zeta5_SourceAnalytic
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-11T23:58:25.612451+00:00
-- url     : https://prove2.me/theorems/d05119c1-1da0-4933-912f-7248f9c50918
-- title:
--   Zeta5: the field $V$ of (6.1) and the weight $\nu$ of (6.10)
-- statement:
--   The two analytic objects of Section 6 of the source attached to the Hankel determinant construction with $K = 40n$, $N = 3n$:
--
--   * the external field of (6.1),$$V(t) \;=\; 2\pi\sqrt{t} + \int_0^1 \log(t+u^2)\,du \;-\; 6\int_0^{\alpha}\log(t+u^2)\,du,\qquad \alpha = \tfrac{3}{40};$$
--
--   * the positive weight of (6.10),$$\nu(y) \;=\; \frac{D_N(y^2)^6}{D_K(y^2)}\, w(y),$$
--
--   where $D_m(t) = \prod_{j=1}^m (t + j^2)$ is the platform definition of the construction module and $w$ is the Bessel-type weight of the moment-weight module. These are exactly the objects in which the energy bound (6.14) and the configuration inequality (6.9) are stated.
--
--   **Formalization Note** Both are `noncomputable def`s in the `Apery` namespace, verbatim from the source modules; no side conditions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Energy.lean#L17-L20 and Apery/Positivity.lean#L116-L118

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_MomentWeight

/-!
# Analytic objects of the Zeta5 construction: the field `V` and the weight `ν`

The external field of (6.1),
`V(t) = 2π√t + ∫₀¹ log(t+u²) du - 6 ∫₀^{α} log(t+u²) du`,  `α = 3/40`,
and the positive weight of (6.10),
`ν(y) = D_N(y²)^6 / D_K(y²) · w(y)`,  `K = 40 n`, `N = 3 n`,

with `D_m` and `w` as defined in the platform definitions
`Definitions.Def_Zeta5_SourceConstruction` and `Definitions.Def_Zeta5_MomentWeight`.

Source: mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Energy.lean` lines 17–20 and `Apery/Positivity.lean` lines 116–118.
-/

open Polynomial MeasureTheory Set

namespace Apery

/-- The external field `V(t)` of (6.1). -/
noncomputable def Vfield (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt t + (∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2)) -
    6 * ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2)

/-- The positive weight `ν(y) = D_N(y²)^6 / D_K(y²) · w(y)` of (6.10), `K = 40 n`, `N = 3 n`. -/
noncomputable def ν (n : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2) (D (3 * n)) ^ 6 / aeval (y ^ 2) (D (40 * n)) * w y

end Apery


