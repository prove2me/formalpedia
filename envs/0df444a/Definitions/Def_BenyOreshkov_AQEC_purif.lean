-- Prove2me | Definitions.Def_BenyOreshkov_AQEC_purif
-- name    : BenyOreshkov_AQEC_purif
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:40.430237+00:00
-- url     : https://prove2.me/theorems/234d0d8c-4be3-46ad-8315-c87cc85c1888
-- title:
--   The canonical purification $|\psi_\rho\rangle\langle\psi_\rho|$ of $\rho$
-- statement:
--   Let $\rho$ be an operator on a finite-dimensional Hilbert space $A$ and let $A_{\mathrm{ref}}$ be a copy of $A$. The **canonical purification** of $\rho$ is the vector
--   $$
--   |\psi_\rho\rangle = \sum_{r,a} (\sqrt\rho)_{a r}\, |r\rangle\otimes|a\rangle \in A_{\mathrm{ref}}\otimes A,
--   $$
--   and `purif ρ` is the rank-one operator $|\psi_\rho\rangle\langle\psi_\rho|$. When $\rho$ is a density matrix, the partial trace over the reference system returns $\rho$, so $|\psi_\rho\rangle$ is a purification of $\rho$, as used in the definition of the entanglement fidelity $F_\rho$.
--
--   **Formalization Note** The reference system is the first tensor factor. $\sqrt\rho$ is the positive square root (`CFC.sqrt`). The paper allows any purification; $F_\rho$ does not depend on the choice, and the canonical one is fixed here.
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, p. 2 ("where |ψ⟩ is a purification of ρ")

import Mathlib

open Matrix
open scoped MatrixOrder

namespace BenyOreshkov.AQEC

/-- **A purification of ρ.** Bény, Oreshkov, arXiv:0907.5391v4, §Main result, p. 2 ("where
|ψ⟩ is a purification of ρ"): the rank-one projector `|ψ_ρ⟩⟨ψ_ρ|` on `A_ref ⊗ A` of the
canonical purification `ψ_ρ(r, a) = (√ρ)_{a r}`, whose reduced state on `A` is `ρ` when `ρ` is a
density matrix.

**Formalization Note** The reference system is a copy of `A` and is the **first** factor (as in
`QAlgorithms.idTensorSuperop`); `√ρ` is `CFC.sqrt ρ`, the positive square root. The paper allows
any purification; the entanglement fidelity does not depend on the choice, so the canonical one
is fixed here. -/
noncomputable def purif {A : Type} [Fintype A] [DecidableEq A] (ρ : Matrix A A ℂ) :
    Matrix (A × A) (A × A) ℂ :=
  Matrix.of fun p q => CFC.sqrt ρ p.2 p.1 * star (CFC.sqrt ρ q.2 q.1)

end BenyOreshkov.AQEC


