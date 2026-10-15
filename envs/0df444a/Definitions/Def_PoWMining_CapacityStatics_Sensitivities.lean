-- Prove2me | Definitions.Def_PoWMining_CapacityStatics_Sensitivities
-- name    : PoWMining_CapacityStatics_Sensitivities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:29.782186+00:00
-- url     : https://prove2.me/theorems/156f7571-6faa-4e30-8f97-8819fd1b33be
-- title:
--   (B.4) — the direct and indirect sensitivities Δ⁽ᵞ⁾ᵢ,₁, Δ⁽ᵞ⁾ᵢ,₂, Δ⁽ᴿ⁾ᵢ,₁, Δ⁽ᴿ⁾ᵢ,₂, defined by derivatives
-- statement:
--   With $f_i(c,\gamma,R;G)$ and $g(c,\gamma,R)$ as in (B.3), the decomposition (B.4) of the sensitivities of an active miner's hash rate to the capacity parameter $\gamma$ and to the reward $R$ defines, at the point $(c,\gamma,R)$,
--   $$\Delta^{(\gamma)}_{i,1} := \frac{\partial f_i}{\partial \gamma},\qquad \Delta^{(\gamma)}_{i,2} := \frac{\partial f_i}{\partial g}\,\frac{\partial g}{\partial \gamma},\qquad \Delta^{(R)}_{i,1} := \frac{\partial f_i}{\partial R},\qquad \Delta^{(R)}_{i,2} := \frac{\partial f_i}{\partial g}\,\frac{\partial g}{\partial R}.$$
--   Here $\partial f_i/\partial\gamma$ and $\partial f_i/\partial R$ are taken with the aggregate argument held fixed at $G = g(c,\gamma,R)$, and $\partial f_i/\partial g$ is the derivative of $f_i$ in its aggregate argument, evaluated at $G = g(c,\gamma,R)$.
--
--   $\Delta_{i,1}$ is the **direct** sensitivity of miner $i$'s hash rate, $\Delta_{i,2}$ the **indirect** one, which acts through the aggregate hash rate.
--
--   **Formalization Note** The four quantities are defined as derivatives (Lean `deriv`), never by their closed forms; the closed forms of the sums are the milestone on (B.4). Where the functions are differentiable, `deriv` is the ordinary derivative; the theorems of the mission assert differentiability via `HasDerivAt`.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 40, (B.4)

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms

namespace PoWMining.CapacityStatics

/-- Direct sensitivity to `γ`, (B.4): `Δ^(γ)ᵢ,₁ := ∂fᵢ/∂γ`, with the aggregate held at `g`. -/
noncomputable def DeltaG1 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun x => PoWMining.CostStatics.fH c x R (PoWMining.CostStatics.gH c γ R) i) γ

/-- Indirect sensitivity to `γ`, (B.4): `Δ^(γ)ᵢ,₂ := (∂fᵢ/∂g)(∂g/∂γ)`. -/
noncomputable def DeltaG2 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun G => PoWMining.CostStatics.fH c γ R G i) (PoWMining.CostStatics.gH c γ R) * deriv (fun x => PoWMining.CostStatics.gH c x R) γ

/-- Direct sensitivity to `R`, (B.4): `Δ^(R)ᵢ,₁ := ∂fᵢ/∂R`, with the aggregate held at `g`. -/
noncomputable def DeltaR1 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun x => PoWMining.CostStatics.fH c γ x (PoWMining.CostStatics.gH c γ R) i) R

/-- Indirect sensitivity to `R`, (B.4): `Δ^(R)ᵢ,₂ := (∂fᵢ/∂g)(∂g/∂R)`. -/
noncomputable def DeltaR2 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  deriv (fun G => PoWMining.CostStatics.fH c γ R G i) (PoWMining.CostStatics.gH c γ R) * deriv (fun x => PoWMining.CostStatics.gH c γ x) R

end PoWMining.CapacityStatics


