-- Prove2me | Definitions.Def_QubitPhaseEst_infidCost
-- name    : QubitPhaseEst_infidCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:23.591985+00:00
-- url     : https://prove2.me/theorems/3c7cbd65-84b3-4932-8c3c-85b39b4f5a00
-- title:
--   Costs: periodicized variance $v(\phi)=4\sin^2\frac\phi2$ and Uhlmann infidelity $1-F(\phi)$
-- statement:
--   Two cost functions of the phase error $\phi$ are used.
--
--   1. The **periodicized variance** $v(\phi)=4\sin^2(\phi/2)$, Eq. (6).
--   2. The **Uhlmann infidelity** between the true one-qubit state $\rho$ and its phase-shifted copy, Eq. (7):
--
--   $$
--   C(\phi)=1-F(\phi),\qquad F(\phi)=\Bigl[\mathrm{Tr}\sqrt{\sqrt{u_\phi\rho u_\phi^\dagger}\;\rho\;\sqrt{u_\phi\rho u_\phi^\dagger}}\Bigr]^2,
--   $$
--
--   where $u_\phi=e^{-i\phi\sigma_z/2}$ is the one-qubit phase shift.
--
--   Both are $2\pi$-periodic and even, and minimizing either averaged cost is the paper's figure of merit.
--
--   **Formalization Note** The root fidelity $\mathrm{Tr}\sqrt{\sqrt{\sigma_1}\sigma_2\sqrt{\sigma_1}}$ is the published `QAlgorithms.rootFidelity`, with $\sigma_1=u_\phi\rho u_\phi^\dagger$ and $\sigma_2=\rho$; it is squared here.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (6) and (7), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QubitPhaseEst_phaseShift

open scoped Matrix

namespace QubitPhaseEst

/-- **The periodicized variance cost** `v(φ) = 4 sin²(φ/2)`, arXiv:quant-ph/0411133v3, Sec. II,
Eq. (6), p. 2. -/
noncomputable def vCost (φ : ℝ) : ℝ :=
  4 * Real.sin (φ / 2) ^ 2

/-- **The Uhlmann infidelity cost** `C(φ) = 1 − F(φ)` of arXiv:quant-ph/0411133v3, Sec. II, Eq. (7),
p. 2, with `F(φ) = [Tr √(√(u_φ ρ u_φ†) ρ √(u_φ ρ u_φ†))]²`, between the one-qubit state `ρ` and its
phase-shifted copy.

**Formalization Note.** The root fidelity is the published `QAlgorithms.rootFidelity`, which is
`Tr √(√σ₁ σ₂ √σ₁)` with `σ₁ = u_φ ρ u_φ†`, `σ₂ = ρ`; it is squared here. The arguments are positive
semidefinite for every state `ρ`, so `cfc` is not at a junk value. -/
noncomputable def infidCost (ρ : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℝ) : ℝ :=
  1 - QAlgorithms.rootFidelity (oneQubitShift φ * ρ * (oneQubitShift φ)ᴴ) ρ ^ 2

end QubitPhaseEst


