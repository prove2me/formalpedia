-- Prove2me | Definitions.Def_StochSQP_Vanishing_Supplement_ShiftedMerit
-- name    : StochSQP_Vanishing_Supplement_ShiftedMerit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:15:07.855348+00:00
-- url     : https://prove2.me/theorems/bde2ad1e-569b-4f82-9697-215f67fea062
-- title:
--   Shifted merit with a genuine objective lower bound
-- statement:
--   For a lower objective bound $f_{\inf}$ along the run, define
--   $$\widetilde\phi(x,\tau)=\tau\bigl(f(x)-f_{\inf}\bigr)+\|c(x)\|_2.$$
--   The bound is any real number satisfying $f_{\inf}\le f(x)$ at every iterate; its sign is unrestricted. This is the shifted merit used in Lemma 19 and the deterministic convergence analysis. The positive sign attached to $f_{\inf}$ in (2) is unnecessary and need not hold for a bounded negative objective. No sign assumption enters the proof on p. 31.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, pp. 4, 30, (2), shifted merit

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

variable {n m : ℕ}

/-- The genuine lower objective bound may have either sign. -/
noncomputable def shiftedMerit (P : Problem n m) (fInf : ℝ) (x : E n) (τ : ℝ) : ℝ :=
  τ * (P.f x - fInf) + ‖P.c x‖

end StochSQP.Vanishing.Supplement


