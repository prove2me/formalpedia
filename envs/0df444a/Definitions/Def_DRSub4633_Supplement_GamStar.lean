-- Prove2me | Definitions.Def_DRSub4633_Supplement_GamStar
-- name    : DRSub4633_Supplement_GamStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:33:16.966309+00:00
-- url     : https://prove2.me/theorems/0e78d811-6c15-47c6-abc2-a567704869ae
-- title:
--   $\Gamma_\star=\alpha_\star^{-1}$, Eq. (136)
-- statement:
--   The intercept constant
--   $$\Gamma_\star=\alpha_\star^{-1}=1+b_\star+\frac1{4b_\star}.$$
--   It differs from the constant $\Gamma=1/\alpha_0$ of the base mission.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53

import Mathlib
import Definitions.Def_DRSub4633_Supplement_alphaStar

namespace DRSub4633.Supplement

/-- **`Γ⋆ = α⋆⁻¹ = 1 + b⋆ + 1/(4b⋆)`, Eq. (136).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53:
"`Γ⋆ = α⋆⁻¹ = 1 + b⋆ + 1/(4b⋆)`". Not the base mission's `Γ` (`DRSub4633.Gam`). -/
noncomputable def GamStar : ℝ := alphaStar⁻¹

end DRSub4633.Supplement


