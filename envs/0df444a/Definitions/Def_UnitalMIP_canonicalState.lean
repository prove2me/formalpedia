-- Prove2me | Definitions.Def_UnitalMIP_canonicalState
-- name    : UnitalMIP_canonicalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:33.444803+00:00
-- url     : https://prove2.me/theorems/4390c2e6-9ef5-4095-b0f7-c19b5e5e9de9
-- title:
--   Correlation channel $\mathcal K_\psi$, canonical states $\psi_{\boldsymbol\lambda}$, local-unitary equivalence, and $\Psi_\lambda$
-- statement:
--   For a two-qubit state $\psi$ the **correlation channel** is the unique linear map $\mathcal K_\psi:M_2\to M_2$ with
--
--   $$
--   \tfrac12\mathrm{Tr}[X\mathcal K_\psi(Y)]=\mathrm{Tr}[(X\otimes Y^T)\psi]\qquad(X,Y\in M_2).
--   $$
--
--   A **canonical state** is $\psi_{\boldsymbol\lambda}=\frac14\sum_{s\in G}\lambda_sP_s\otimes P_s^T$ with real $\lambda_s$ and $\lambda_0=1$. Two two-qubit operators are **locally unitarily equivalent** if $(U_A\otimes U_B)\psi(U_A\otimes U_B)^\dagger=\varphi$ for single-qubit unitaries $U_A,U_B$. The **boundary canonical form** is
--
--   $$
--   \Psi_\lambda=\tfrac12\bigl(|00\rangle\langle00|+|11\rangle\langle11|+\lambda|00\rangle\langle11|+\lambda|11\rangle\langle00|\bigr).
--   $$
--
--   Canonical forms reduce every state with maximally mixed marginals to diagonal Pauli form; $\Psi_\lambda$ is the form at $\rho_{\max}=1$.
--
--   **Formalization Note** $\mathcal K_\psi$ is written out entrywise, $\mathcal K_\psi(Y)_{ij}=2\,\mathrm{Tr}[(E_{ji}\otimes Y^T)\psi]$, which satisfies the defining identity (a proved sanity check). The condition $\lambda_0=1$ is stated where canonical states are used.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Definition 2.24, p.19; Definition 2.27, p.20; (27), p.30

import Mathlib
import Definitions.Def_UnitalMIP_pauliString

open scoped Matrix

namespace UnitalMIP

/-- The **correlation channel** `K_ψ : M₂ → M₂` of a two-qubit state `ψ` (arXiv:2609.39318,
version of 2026-11-03, sha256 56ebc59e…, Definition 2.24, p.19): the unique linear map with
`½ Tr[X K_ψ(Y)] = Tr[(X ⊗ Y^T) ψ]` for all `X, Y ∈ M₂`.

**Formalization Note** The map is written out: `K_ψ(Y)_{ij} = 2 Tr[(E_{ji} ⊗ Y^T) ψ]` with `E_{ji}`
the matrix unit. Since `Tr[X M] = ∑_{ij} X_{ji} M_{ij}` and `X = ∑ X_{ji} E_{ji}`, this map satisfies
the defining identity, and the identity determines it (the trace pairing is nondegenerate). It is
total: it is applied to states with maximally mixed marginals, as in the source. -/
noncomputable def corrChannel (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    QAlgorithms.Superop (Fin 2) (Fin 2) :=
  fun Y => Matrix.of fun i j =>
    2 * Matrix.trace (Matrix.kronecker (Matrix.single j i (1 : ℂ)) Yᵀ * ψ)

/-- The **canonical state** `ψ_λ := ¼ ∑_{s ∈ G} λ_s P_s ⊗ P_s^T` with real `λ_s`
(arXiv:2609.39318, version of 2026-11-03, Definition 2.27, p.20). The source requires `λ₀ = 1`;
that condition is stated where the definition is used. -/
noncomputable def canonicalState (lam : Fin 2 × Fin 2 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • ∑ s : Fin 2 × Fin 2, ((lam s : ℂ)) • Matrix.kronecker (pauli s) (pauli s)ᵀ

/-- **Local-unitary equivalence** of two two-qubit operators (arXiv:2609.39318, version of
2026-11-03, Definition 2.27 and Proposition 2.28, p.20; Proposition 3.8, p.30): there are
single-qubit unitaries `U_A`, `U_B` with `(U_A ⊗ U_B) ψ (U_A ⊗ U_B)† = φ`. -/
def IsLUEquiv (ψ φ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∃ UA ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ UB ∈ Matrix.unitaryGroup (Fin 2) ℂ,
    Matrix.kronecker UA UB * ψ * (Matrix.kronecker UA UB)ᴴ = φ

/-- The **boundary canonical form**
`Ψ_λ := ½(|00⟩⟨00| + |11⟩⟨11| + λ|00⟩⟨11| + λ|11⟩⟨00|)` (arXiv:2609.39318, version of
2026-11-03, (27), p.30). -/
noncomputable def PsiBoundary (lam : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    if p.1 = p.2 ∧ q.1 = q.2 then (if p.1 = q.1 then (1 / 2 : ℂ) else (lam : ℂ) / 2) else 0

end UnitalMIP


