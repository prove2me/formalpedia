-- Prove2me | Definitions.Def_DRSub4633_lam
-- name    : DRSub4633_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:17.391613+00:00
-- url     : https://prove2.me/theorems/fb35cbcf-7bde-497a-9dac-e2fc9b453ade
-- title:
--   The weight $\lambda=w+\kappa_0-\kappa$
-- statement:
--   The small-coordinate weight
--   $$\lambda(t)=w(t)+\kappa_0(t)-\kappa(t).$$
--   It vanishes before $t_0$ and equals $w-bW$ afterwards.
--
--   **Formalization Note** `λ` is reserved in Lean; the weight is named `lam`.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (19), p.11

import Mathlib
import Definitions.Def_DRSub4633_wDens
import Definitions.Def_DRSub4633_kappa0
import Definitions.Def_DRSub4633_kappa

namespace DRSub4633

/-- **The small-coordinate weight `λ(t) = w(t) + κ₀(t) − κ(t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1,
Eq. (19), p.11.

**Formalization Note.** `λ` is a reserved word in Lean; the weight is named `lam`. -/
noncomputable def lam (t : ℝ) : ℝ := wDens t + kappa0 t - kappa t

end DRSub4633


