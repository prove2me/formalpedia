-- Prove2me | Definitions.Def_QubitPhaseEst_phaseShift
-- name    : QubitPhaseEst_phaseShift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:32.605478+00:00
-- url     : https://prove2.me/theorems/f4606aac-69bb-4e1d-8f8b-e338245d74aa
-- title:
--   Phase shift $U_\phi=e^{-i\phi J_z}$ on $N$ qubits
-- statement:
--   Let $J_z=\tfrac12\sum_{k=1}^N\sigma_z^{(k)}$ be the total angular momentum along $z$ of $N$ qubits. On the computational basis vector $|x\rangle$ it has the eigenvalue
--
--   $$
--   m(x)=\sum_{k=1}^N\Bigl(\tfrac12\ \text{if } x_k=0,\ -\tfrac12\ \text{if } x_k=1\Bigr).
--   $$
--
--   The **phase shift** by the angle $\phi\in\mathbb R$ is the unitary
--
--   $$
--   U_\phi=e^{-i\phi J_z}=\sum_x e^{-i\phi\, m(x)}\,|x\rangle\langle x| = \bigl(e^{-i\phi\sigma_z/2}\bigr)^{\otimes N}.
--   $$
--
--   The one-qubit factor $u_\phi=e^{-i\phi\sigma_z/2}=\mathrm{diag}(e^{-i\phi/2},e^{i\phi/2})$ is defined as well; it is the phase shift of a single qubit, used in the fidelity cost.
--
--   The unknown parameter of the estimation problem is $\phi$; it is imprinted on the $N$ copies of the state by $U_\phi$.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (1), p. 1; Eq. (7), p. 2 (u_φ for one qubit)

import Mathlib
import Definitions.Def_QubitPhaseEst_Qb

open scoped Matrix

namespace QubitPhaseEst

/-- The eigenvalue of `J_z = ½ Σ_k σ_z^{(k)}` on the computational basis vector `|x⟩`: each bit
`0` contributes `+½`, each bit `1` contributes `−½`. arXiv:quant-ph/0411133v3, Sec. II, p. 1. -/
noncomputable def mz {N : ℕ} (x : Qb N) : ℝ :=
  ∑ k, if x k = 0 then (1 / 2 : ℝ) else -1 / 2

/-- **The phase shift `U_φ = e^{−iφJ_z}`** on `N` qubits, arXiv:quant-ph/0411133v3, Sec. II, Eq. (1),
p. 1. `J_z` is diagonal in the computational basis, so this is the diagonal matrix with entries
`e^{−iφ m(x)}`; it equals `(e^{−iφσ_z/2})^{⊗N}`. -/
noncomputable def phaseShift (N : ℕ) (φ : ℝ) : Matrix (Qb N) (Qb N) ℂ :=
  Matrix.diagonal fun x => Complex.exp (-((φ : ℂ) * (mz x : ℂ)) * Complex.I)

/-- The one-qubit phase shift `u_φ = e^{−iφσ_z/2} = diag(e^{−iφ/2}, e^{iφ/2})` of
arXiv:quant-ph/0411133v3, Sec. II, Eqs. (1), (7), pp. 1–2.

**Formalization Note.** Written directly on `Fin 2`, not transported from `phaseShift 1 φ`; both
have the same entries under `Qb 1 ≃ Fin 2`. -/
noncomputable def oneQubitShift (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp (-((φ : ℂ) / 2) * Complex.I), Complex.exp (((φ : ℂ) / 2) * Complex.I)]

end QubitPhaseEst


