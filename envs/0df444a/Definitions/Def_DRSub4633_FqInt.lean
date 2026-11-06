-- Prove2me | Definitions.Def_DRSub4633_FqInt
-- name    : DRSub4633_FqInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:03:41.519233+00:00
-- url     : https://prove2.me/theorems/9515ed01-a54e-4003-9208-fe67976140b7
-- title:
--   The constant-profile integrand $F_q$
-- statement:
--   For a constant $q\in\mathbb R$,
--   $$F_q(t)=\Lambda(q)W(t)+\mathfrak c(q)\lambda(t)-\Gamma.$$
--
--   **Formalization Note** Named `FqInt` to avoid a clash with the residual $F$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix A, Eq. (118), p.43

import Mathlib
import Definitions.Def_DRSub4633_LamFun
import Definitions.Def_DRSub4633_cFun
import Definitions.Def_DRSub4633_WTail
import Definitions.Def_DRSub4633_lam
import Definitions.Def_DRSub4633_Gam

namespace DRSub4633

/-- **The constant-profile integrand `F_q(t) = Λ(q)W(t) + 𝔠(q)λ(t) − Γ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix A,
Eq. (118), p.43 ("For a constant `q ∈ ℝ`").

**Formalization Note.** Named `FqInt` to avoid a clash with the residual `F`. -/
noncomputable def FqInt (q t : ℝ) : ℝ := LamFun q * WTail t + cFun q * lam t - Gam

end DRSub4633


