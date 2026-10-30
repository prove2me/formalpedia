-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_xiStar
-- name    : DigitalPrivacy_DataStrategy_xiStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:07:42.595552+00:00
-- url     : https://prove2.me/theorems/2e8cfbeb-8845-4b04-8a20-611eae7e90fd
-- title:
--   Optimal data collection $\xi^\star$, display (5)
-- statement:
--   Define
--
--   $$\xi^\star=\begin{cases}1,&\psi\le P\rho,\\ \max\{0,\min\{1,\xi_i\}\},&\psi>P\rho.\end{cases}$$
--
--   This is display (5), $\xi^\star=\max\{0,\min\{1,\frac1{2P\rho}(-(1-P)\rho-P+|P-(1-P)\rho|\sqrt{\psi/\max\{0,\psi-P\rho\}})\}\}$.
--
--   **Formalization Note** For $\psi\le P\rho$ the term $\psi/\max\{0,\psi-P\rho\}$ divides by $0$; the proof reads it as $+\infty$, which makes $\xi^\star=1$ (p. 31). Lean's $x/0=0$ would give $0$, so this case is an explicit branch. $\xi_i$ is extended to $P\rho=0$ as described for $\xi_i$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Theorem 1, display (5), p. 11 (PDF 12); reading of ψ/max{0, ψ − Pρ} from App. A.2, p. 31 (PDF 32)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_xiI

namespace DigitalPrivacy.DataStrategy

/-- **The optimal data collection `ξ*`, display (5).**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Theorem 1, display (5), p. 11 (PDF 12): "ξ⋆ = max{0, min{1, (1/(2Pρ))(−(1 − P)ρ − P +
|P − (1 − P)ρ| · √(ψ/max{0, ψ − Pρ}))}}".

`xiStar ρ P ψ = 1` if `ψ ≤ Pρ`, and otherwise `max{0, min{1, ξᵢ}}` with `ξᵢ = xiI ρ P ψ`.

**Formalization Note.** For `ψ ≤ Pρ` the printed `ψ/max{0, ψ − Pρ}` divides by `0`; the proof
reads it as `+∞`: the `max{0, ψ − Pρ}` "turns ξi into ∞ (and, thus guarantees that ξ⋆ = 1 is
chosen) when ψ < Pρ < ψL" (App. A.2, p. 31). Lean's `x/0 = 0` would give the wrong value `0`,
so that case is the explicit branch `1`. For `ψ > Pρ` the expression is the printed one, with
`ξᵢ` extended to `Pρ = 0` as in `xiI`. -/
noncomputable def xiStar (ρ P ψ : ℝ) : ℝ :=
  if ψ ≤ P * ρ then 1 else max 0 (min 1 (xiI ρ P ψ))

end DigitalPrivacy.DataStrategy


