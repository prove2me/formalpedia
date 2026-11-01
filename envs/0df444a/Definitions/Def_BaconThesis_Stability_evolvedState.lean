-- Prove2me | Definitions.Def_BaconThesis_Stability_evolvedState
-- name    : BaconThesis_Stability_evolvedState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:23.011209+00:00
-- url     : https://prove2.me/theorems/410e5f14-b067-40ff-89a2-372dcb58ca56
-- title:
--   Reduced evolution $\rho(t)=\mathrm{Tr}_E[U(t)(\rho(0)\otimes\rho_E)U(t)^\dagger]$, $U(t)=e^{-iHt}$
-- statement:
--   Let a system $S$ and an environment $E$ have finite-dimensional Hilbert spaces and let $H$ be an operator on $S\otimes E$ (the Hamiltonian). For an initial system state $\rho(0)$ and an initial environment state $\rho_E$, uncorrelated with the system, the state of the system at time $t\in\mathbb R$ is
--   $$
--   \rho(t)=\mathrm{Tr}_E\!\left[U(t)\,\big(\rho(0)\otimes\rho_E\big)\,U(t)^\dagger\right],\qquad U(t)=\exp[-iHt]
--   $$
--   (with $\hbar=1$).
--
--   This is the operator-sum evolution of the system whose decoherence rates Chapter 6 studies, with $H=H_{SB}+\epsilon H'_I$ the perturbed Hamiltonian of eq. (6.4).
--
--   **Formalization Note** The system-environment index is $S\times E$ (system first) and $\rho(0)\otimes\rho_E$ is the Kronecker product; the exponential is Mathlib's matrix exponential of $(-it)\cdot H$; $\mathrm{Tr}_E$ is `WildeQIT.partialTraceRight`. No Hermiticity is built in; the theorems assume it.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, eq. (6.4), p.88 (PDF p.105)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

open scoped Kronecker Matrix

namespace BaconThesis.Stability

/-- **The evolved system state `ρ(t) = Tr_E[U(t)(ρ(0) ⊗ ρ_E)U(t)†]`, `U(t) = exp[−iHt]`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, eq. (6.4), p.88 (PDF p.105) (`U'(t) = exp[−iH'_{SB} t]`), with the reduced dynamics of
§2.2.1 (the operator-sum representation of the system's evolution under a system-environment
Hamiltonian, the environment initially in `ρ_E` and uncorrelated with the system).

For a Hamiltonian `H` on the system-environment space, a system state `ρ0` and an environment
state `ρE`, `evolvedState H ρ0 ρE t` is the partial trace over the environment of
`U(t) (ρ0 ⊗ ρE) U(t)†` with `U(t) = exp(−i t H)`.

**Formalization Note.** Hilbert spaces are `S → ℂ`, `E → ℂ` with finite index types; the
system-environment space is indexed by `S × E` (system first) and `ρ0 ⊗ ρE` is the Kronecker
product. The exponential is Mathlib's matrix exponential `NormedSpace.exp` of `(−i t) • H`; the
time `t` is any real and `ħ = 1`. `Tr_E` is `WildeQIT.partialTraceRight`. No Hermiticity is built
in; the theorems assume it. -/
noncomputable def evolvedState {S E : Type} [Fintype S] [DecidableEq S] [Fintype E]
    [DecidableEq E] (H : Matrix (S × E) (S × E) ℂ) (ρ0 : Matrix S S ℂ) (ρE : Matrix E E ℂ)
    (t : ℝ) : Matrix S S ℂ :=
  WildeQIT.partialTraceRight
    (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H) * (ρ0 ⊗ₖ ρE) *
      (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H))ᴴ)

end BaconThesis.Stability


