-- Prove2me | Definitions.Def_Zeta5_SourcePullback
-- name    : Zeta5_SourcePullback
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T19:30:26.473252+00:00
-- url     : https://prove2.me/theorems/1314704a-ac32-4e19-841f-a94c52104062
-- title:
--   The pullback map pull K P = (-1)^K x^5 P(-x^2) and the cofactors B_j
-- statement:
--   This module reproduces the pullback map of `Apery/Arith/Pullback.lean` of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: `pull K P = (-1)^K x^5 P(-x^2)`, the substitution turning the rational function $P/D_K$ into a rational function with the simple integer poles $\pm 1, \dots, \pm K$ (so that the functional $\tau_X$ applies), and the cofactors `Bj K j = (-1)^K ∏_{i ≠ j} (i² - x²)` appearing in the partial-fraction expansion. The pullback identity $\mu_X(P/D_K) = \tau_X(\mathrm{pull}\,K\,P, PlK\,K)$ is proved in `Apery.muX_eq_tauX`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/Pullback.lean#L114-L125

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourcePoleFun

/-!
# The pullback map of the Apery proof (`Apery/Arith/Pullback.lean`)

* `pull K P = (-1)^K x^5 P(-x²)` — the substitution that turns the rational function
  `P/D_K` in `x` into a rational function with the simple integer poles `±1, …, ±K`;
* `Bj K j = (-1)^K ∏_{i ≠ j} (i² - x²)` — the cofactor in the partial-fraction expansion.

Nothing is proved here; reproduced verbatim from mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0. The pullback identity
`μ_X(P/D_K) = τ_X(pull K P, PlK K)` is proved in `Apery.μX_eq_tauX`.
-/

open Finset Polynomial

namespace Apery

/-- `pull K P = (-1)^K x⁵ P(-x²)`. -/
noncomputable def pull (K : ℕ) (P : ℚ[X]) : ℚ[X] := C ((-1 : ℚ) ^ K) * X ^ 5 * P.comp (-X ^ 2)

/-- The cofactor `B_j = (-1)^K ∏_{i ≠ j} (i² - x²)`. -/
noncomputable def Bj (K j : ℕ) : ℚ[X] :=
  C ((-1 : ℚ) ^ K) * (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).comp (-X ^ 2)

end Apery


