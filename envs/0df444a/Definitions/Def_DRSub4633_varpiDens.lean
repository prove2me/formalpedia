-- Prove2me | Definitions.Def_DRSub4633_varpiDens
-- name    : DRSub4633_varpiDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:44.30619+00:00
-- url     : https://prove2.me/theorems/1401fb8e-c5d9-4202-b47e-75cf2befc447
-- title:
--   The density $\varpi$
-- statement:
--   With $\varpi_0=1524341/24250000$ and $\varpi_1=24171693/9409000$,
--   $$\varpi(t)=[\varpi_0+\varpi_1(t-t_0)]\,\mathbf 1_{[t_0,t_1]}(t).$$
--   It is the density with which the direct large-block comparison (41) is averaged.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eqs. (17)–(18), p.11

import Mathlib
import Definitions.Def_DRSub4633_t0
import Definitions.Def_DRSub4633_t1

namespace DRSub4633

/-- **The density `ϖ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eqs. (17)–(18), p.11:
`ϖ(t) = [ϖ₀ + ϖ₁(t − t₀)] 1_[t₀,t₁](t)` with `ϖ₀ = 1524341/24250000`, `ϖ₁ = 24171693/9409000`.

**Formalization Note.** The constants `ϖ₀, ϖ₁` of (17) are written as literals. -/
noncomputable def varpiDens (t : ℝ) : ℝ :=
  if t0 ≤ t ∧ t ≤ t1 then 1524341 / 24250000 + (24171693 / 9409000) * (t - t0) else 0

end DRSub4633


