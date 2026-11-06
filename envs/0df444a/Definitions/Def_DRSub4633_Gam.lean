-- Prove2me | Definitions.Def_DRSub4633_Gam
-- name    : DRSub4633_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:17.862075+00:00
-- url     : https://prove2.me/theorems/f6335aa6-8de2-42ee-9735-92e0710a9fee
-- title:
--   The constant $\Gamma=1+b+1/(4b)$
-- statement:
--   The constant
--   $$\Gamma=1+b+\frac1{4b}=\frac{117486474169}{54440750000}.$$
--   It multiplies $f(h(x))$ in the affine comparison (25); its inverse is the approximation coefficient $\alpha_0$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (8), p.9

import Mathlib
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The constant `Γ = 1 + b + 1/(4b)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (8), p.9:
"`Γ = 1 + b + 1/(4b) = 117486474169/54440750000`". -/
noncomputable def Gam : ℝ := 1 + bPar + 1 / (4 * bPar)

end DRSub4633


