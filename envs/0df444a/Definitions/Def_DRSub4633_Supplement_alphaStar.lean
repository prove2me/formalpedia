-- Prove2me | Definitions.Def_DRSub4633_Supplement_alphaStar
-- name    : DRSub4633_Supplement_alphaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:32:33.909481+00:00
-- url     : https://prove2.me/theorems/56c19fc1-840b-43f3-901a-aac95c639b48
-- title:
--   $\alpha_\star=b_\star/(1+b_\star)=2\sqrt3-3$, Eq. (136)
-- statement:
--   The sharp recovery coefficient
--   $$\alpha_\star=\frac{b_\star}{1+b_\star}=2\sqrt3-3\approx0.4641 .$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53

import Mathlib
import Definitions.Def_DRSub4633_Supplement_bStar

namespace DRSub4633.Supplement

/-- **`α⋆ = b⋆/(1 + b⋆) = 2√3 − 3`, Eq. (136).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53:
"`α⋆ = b⋆/(1 + b⋆) = 2√3 − 3`". -/
noncomputable def alphaStar : ℝ := bStar / (1 + bStar)

end DRSub4633.Supplement


