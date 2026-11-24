-- Prove2me | Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply
-- name    : TwoSidedExp_DemandLimit_Supplement_Supply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:17:57.193565+00:00
-- url     : https://prove2.me/theorems/0ec7f402-5105-4c43-ad5d-f7f50afd3ea5
-- title:
--   Supply-constrained choice weight g
-- statement:
--   For customer condition i and listing condition j, let α_{γ,i}(θ,j), v_{γ,i}(θ,j) and ϵ_{γ,i} be the published experimental parameters. Define
--
--   $$g_{\gamma,i}(\theta,j)=\frac{\alpha_{\gamma,i}(\theta,j)v_{\gamma,i}(\theta,j)}{\epsilon_{\gamma,i}}.$$
--
--   The parameters are independent of treatment shares, so they may be read from the experimental system with shares (1,1). This weight appears in both the first-order availability expansion and the booking-rate limit of Proposition 3.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 20, §6.1.2, before Proposition 3

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

/-- g from §6.1.2, p. 20. The choice parameters do not depend on treatment shares. -/
noncomputable def g (M : Model Γ Θ) (q : Γ × Fin 2) (p : Θ × Fin 2) : ℝ :=
  (M.expt 1 1).α q p * (M.expt 1 1).v q p / (M.expt 1 1).eps q

end TwoSidedExp.DemandLimit.Supplement


