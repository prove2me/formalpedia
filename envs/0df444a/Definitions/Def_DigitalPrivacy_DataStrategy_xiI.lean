-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_xiI
-- name    : DigitalPrivacy_DataStrategy_xiI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:54.073538+00:00
-- url     : https://prove2.me/theorems/15e899f6-3db7-4d43-bb65-7ba884a71117
-- title:
--   Interior root $\xi_i$ of $C_{{inv}}=C_h$
-- statement:
--   Let $a=P+(1-P)\rho$. Define
--
--   $$\xi_i=\frac1{2P\rho}\Big(-(1-P)\rho-P+|P-(1-P)\rho|\sqrt{\frac{\psi}{\psi-P\rho}}\Big)\quad\text{if }P\rho>0,$$
--
--   $\xi_i=\dfrac{a^2-4\psi(1-P)}{4a\psi}$ if $P\rho=0<a$, and $\xi_i=0$ if $P=\rho=0$.
--
--   For $\psi>P\rho$, $\xi_i$ is the positive root (when one exists) of $C_{inv}(\xi)=C_h(\xi)$, i.e. of $4P\rho(\psi-P\rho)\xi^2+4a(\psi-P\rho)\xi+4\psi(1-P)-a^2=0$, and it gives the interior optimal collection.
--
--   **Formalization Note** The paper's formula divides by $2P\rho$, which vanishes at $P=0$ (the purely usage-driven business) and at $\rho=0$. There the equation is linear and its root, also the limit of the printed formula as $P\rho\to0$, is used; when $P=\rho=0$ there is no positive root and the branch is $0$ explicitly. Meant for $\psi>P\rho$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered; extension to Pρ = 0 (correction C2)

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **The interior root `ξᵢ` of `C_inv(ξ) = C_h(ξ)`, extended to `Pρ = 0`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered: "Solve Cinv(ξ) = Ch(ξ). We get
two non-negative roots: ξ = 0 and ξi = (1/(2Pρ))(−(1−P)ρ − P + |P − (1−P)ρ| √(ψ/(ψ−Pρ)))."

* If `Pρ > 0`: the printed formula.
* If `Pρ = 0` and `a := P + (1 − P)ρ > 0`: `(a² − 4ψ(1 − P))/(4aψ)`.
* Otherwise (`P = ρ = 0`): `0`.

**Formalization Note.** The printed formula divides by `2Pρ`, which vanishes for the purely
usage-driven business `P = 0` and for `ρ = 0`. There the equation `C_inv(ξ) = C_h(ξ)`, i.e.
`4Pρ(ψ − Pρ)ξ² + 4a(ψ − Pρ)ξ + 4ψ(1 − P) − a² = 0`, is linear, and its root
`(a² − 4ψ(1 − P))/(4aψ)` is also the limit of the printed formula as `Pρ → 0`. When `P = ρ = 0`
the equation has no positive root and the optimum is `ξ* = 0`; that branch is `0` explicitly
instead of relying on a division by zero. Meant for `ψ > Pρ`. -/
noncomputable def xiI (ρ P ψ : ℝ) : ℝ :=
  if 0 < P * ρ then
    (1 / (2 * P * ρ)) * (-(1 - P) * ρ - P + |P - (1 - P) * ρ| * Real.sqrt (ψ / (ψ - P * ρ)))
  else if 0 < P + (1 - P) * ρ then
    ((P + (1 - P) * ρ) ^ 2 - 4 * ψ * (1 - P)) / (4 * (P + (1 - P) * ρ) * ψ)
  else 0

end DigitalPrivacy.DataStrategy


