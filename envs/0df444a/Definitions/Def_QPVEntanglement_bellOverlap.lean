-- Prove2me | Definitions.Def_QPVEntanglement_bellOverlap
-- name    : QPVEntanglement_bellOverlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:20.237723+00:00
-- url     : https://prove2.me/theorems/71ac5bcc-b97f-4cb3-bd9e-a28b2c3e689b
-- title:
--   The Bell state $\Phi^+$ and the fidelity $F(\rho,\Phi^+)$
-- statement:
--   On two qubits $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ and $\Phi^+=|\Phi^+\rangle\langle\Phi^+|$. The fidelity with $\Phi^+$ is $F(\rho,\Phi^+)=\langle\Phi^+|\rho|\Phi^+\rangle$: the paper's $F$ is the squared Uhlmann fidelity, which against a pure state is this overlap.
--
--   **Formalization Note** The trace distance $\mathrm{TD}[\rho,\sigma]=\tfrac12\|\rho-\sigma\|_1$ used by the mission is the published `RandPurIso.Completion.traceDist` (full trace norm `QAlgorithms.traceNorm`), referenced, not redefined.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §3, p.26

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_RandPurIso_Completion_traceDist

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- The Bell vector `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` on two qubits (§3, p.26). -/
noncomputable def phiPlusVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The Bell state `Φ⁺ = |Φ⁺⟩⟨Φ⁺|` (§3, p.26). -/
noncomputable def phiPlus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.vecMulVec phiPlusVec (star phiPlusVec)

/-- **The fidelity with the Bell state** `F(ρ, Φ⁺) = ⟨Φ⁺|ρ|Φ⁺⟩` of a two-qubit state (§3, p.26).
Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), §3, p.26: "If
`σ = |ψ⟩⟨ψ|` is pure, then `F(ρ, σ) = ⟨ψ|ρ|ψ⟩`"; the paper's `F` is the squared Uhlmann
fidelity).

**Formalization Note.** The trace distance `TD[ρ, σ] = ½‖ρ − σ‖₁` (§3, p.26) of the mission is the
published `RandPurIso.Completion.traceDist`, imported here. -/
noncomputable def bellOverlap (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (star phiPlusVec ⬝ᵥ ρ.mulVec phiPlusVec).re

end QPVEntanglement


