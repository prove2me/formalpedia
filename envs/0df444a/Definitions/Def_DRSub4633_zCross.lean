-- Prove2me | Definitions.Def_DRSub4633_zCross
-- name    : DRSub4633_zCross
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:00.620704+00:00
-- url     : https://prove2.me/theorems/0be3f0af-bba2-47ec-b9ee-09be9b779214
-- title:
--   The crossing point $z$
-- statement:
--   The crossing point $z$ is the unique $z\in(0,1)$ with
--   $$\int_0^z e^{-st}\rho_1(t)\,dt=1 .$$
--   It is where the auxiliary functions $\theta_+$ and $\theta_-$ cross.
--
--   **Formalization Note** $z$ is defined as the infimum of the $t\in[0,1]$ with $\int_0^t e^{-sr}\rho_1(r)\,dr\ge 1$. The integral is continuous and strictly increasing, vanishes at $0$ and exceeds $1$ at $t=1$, so the infimum is the root above; the definition does not assume these facts.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.12

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_rho1

namespace DRSub4633

/-- **The crossing point `z`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.12: "there is a unique `z ∈ (0, 1)` with
`∫_0^z e^(−st) ρ₁(t) dt = 1`."

**Formalization Note.** `z` is defined as the infimum of the times `t ∈ [0, 1]` at which
`∫_0^t e^(−sr) ρ₁(r) dr ≥ 1`. Since this integral is continuous and strictly increasing in `t`, is
`0` at `t = 0` and exceeds `1` at `t = 1` (p.12), the infimum is the unique root of the page. The
definition does not assume these facts (Lemma A.2 proves `z > 3/4`). -/
noncomputable def zCross : ℝ :=
  sInf {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ 1 ≤ ∫ r in (0 : ℝ)..t, Real.exp (-(sPar * r)) * rho1 r}

end DRSub4633


