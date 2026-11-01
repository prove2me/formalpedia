-- Prove2me | Definitions.Def_QubitPhaseEst_Qb
-- name    : QubitPhaseEst_Qb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:50.382647+00:00
-- url     : https://prove2.me/theorems/8122191a-fad9-4f6f-b6df-c46a61f0fb1e
-- title:
--   Computational basis $\{0,1\}^N$ of $N$ qubits
-- statement:
--   The **computational basis** of a register of $N$ qubits is labelled by bit strings $x=(x_1,\dots,x_N)\in\{0,1\}^N$. Bit $0$ is the eigenvector of $\sigma_z$ with eigenvalue $+1$ (spin up) and bit $1$ the eigenvector with eigenvalue $-1$ (spin down). Operators on the $N$ qubits are $2^N\times 2^N$ complex matrices indexed by these labels.
--
--   This is the carrier of every object of the mission: the product state $R_{\vec n}=\rho_{\vec n}^{\otimes N}$, the phase shift $U_\phi$, and the seeds $\xi$ of covariant measurements.
--
--   **Formalization Note** The label type is `Fin N → Fin 2`, the index type of the published tensor power `ShadowTomography.UpperBound.tensorPow`.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, p. 1, unnumbered (the N qubits of Eq. (1))

import Mathlib

namespace QubitPhaseEst

/-- **The computational basis of `N` qubits.** D'Ariano, Macchiavello, Perinotti, *Optimal phase
estimation for qubit mixed states*, arXiv:quant-ph/0411133v3, Sec. II, unnumbered, p. 1: the `N`
qubits on which the phase shift `U_φ` acts. A basis label is a bit string `x : Fin N → Fin 2`.

**Formalization Note.** Bit `0` is the `σ_z` eigenvalue `+1` (spin up) and bit `1` is `−1`.
Operators on `N` qubits are matrices `Matrix (Qb N) (Qb N) ℂ`; the state `R_n = ρ_n^{⊗N}` is the
published `ShadowTomography.UpperBound.tensorPow ρ_n N`, whose index type `Fin N → Fin 2` is `Qb N`. -/
abbrev Qb (N : ℕ) := Fin N → Fin 2

end QubitPhaseEst


