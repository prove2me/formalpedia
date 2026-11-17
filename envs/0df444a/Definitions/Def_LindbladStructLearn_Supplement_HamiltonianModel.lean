-- Prove2me | Definitions.Def_LindbladStructLearn_Supplement_HamiltonianModel
-- name    : LindbladStructLearn_Supplement_HamiltonianModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:39:50.376917+00:00
-- url     : https://prove2.me/theorems/a09cab35-395c-41a0-bc8b-cf5a35f6d5e8
-- title:
--   Hamiltonians $H(x)=i\sum_P x_P P$, real-time evolution $e^{-iHt}$ and Gibbs-state access
-- statement:
--   Section 5.6 of the paper learns a $k$-local Hamiltonian
--   $$H(x)=i\sum_{P\in\mathcal P_k}x_P\,P,$$
--   where $\mathcal P_k$ is the set of non-identity $n$-qubit Paulis acting on at most $k$ qubits and $x\in\mathbb C^{\mathcal P_k}$ is a coefficient vector. The factor $i$ makes $H(x)$ Hermitian exactly when every $x_P$ is purely imaginary, matching the coherent part of a Lindbladian in Section 2.1. This module defines:
--
--   1. the index set $\mathcal P_k$ (`HIdx n k`);
--   2. the operator $H(x)$ (`hamOp`), for every complex vector $x$;
--   3. the embedding of $x$ as a Lindbladian coefficient vector with $\lambda_{(P,I)}=x_P$ and all other entries $0$ (`hamVec`). Through it the published local one-norm gives $\|x\|_{B_1}=\max_i\sum_{P\ni i}|x_P|$, and the published degree gives the largest number of nonzero terms acting on one qubit;
--   4. real-time evolution $\rho\mapsto e^{-iH(\lambda)\tau}\rho\, e^{iH(\lambda)\tau}$ (`rtChannel`);
--   5. Gibbs-state access, the replacement channel $\rho\mapsto \operatorname{tr}(\rho)\,\rho_\beta$ with $\rho_\beta=e^{-\beta H(\lambda)}/\operatorname{tr}(e^{-\beta H(\lambda)})$ (`gibbsChannel`). Fed a prepared state, it returns a fresh copy of $\rho_\beta$.
--
--   These are the two access models of Theorems 5.13 and 5.18, and the objects that Theorem 5.11 iterates over.
--
--   **Formalization Note** Pauli letters $0,1,2,3$ are $I,X,Y,Z$ and qubits are indexed $0,\dots,n-1$. The Gibbs state is the published `WolfAreaLaw.thermalState`. The evolution is the published `conjugation` by the matrix exponential.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §5.6, Eq. (5.126), p.46; Theorem 5.13, p.48; Theorem 5.18, p.52

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_WolfAreaLaw_thermalState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing

/-- The index set of a `k`-local Hamiltonian's coefficient vector (Lewis–Tang–Wright, *Learning the
structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §5.6,
p.46): the non-identity Paulis `P` with `|supp P| ≤ k` (the paper's `𝒫_k`, the index set of `F`).

**Formalization Note** Pauli letters `0,1,2,3 = I,X,Y,Z`; qubits are `Fin n` (0-based). -/
abbrev HIdx (n k : ℕ) : Type :=
  {P : Pauli n // P ≠ 0 ∧ (support P).card ≤ k}

/-- The Hamiltonian of a coefficient vector (§5.6, p.46): `H(x) = i Σ_P x_P P`, the sum over the
`k`-local non-identity Paulis. For purely imaginary `x` this is Hermitian; it is defined for every
complex `x` (the iterates of Algorithm 5 are complex vectors). -/
noncomputable def hamOp {n k : ℕ} (x : HIdx n k → ℂ) : Op (Qubits n) :=
  Complex.I • ∑ P : HIdx n k, x P • pauliMatrix P.1

/-- A Hamiltonian coefficient vector as a coefficient vector on pairs of Paulis (§2.1, p.13: the
coherent part `α_P = λ_(P,I)`): the entry of `(P, I)` is `x_P`, every other entry is `0`. Used only to
apply the published local one-norm `b1Norm` (`‖x‖_B1 = max_i Σ_(P ∋ i) |x_P|`, Definition 2.4) and
degree `deg` (every qubit is in at most `deg` nonzero terms, Eq. (2.8)) to a Hamiltonian, since the
support of `(P, I)` is the support of `P`. -/
noncomputable def hamVec {n k : ℕ} (x : HIdx n k → ℂ) : Pauli n × Pauli n → ℂ := fun P =>
  if h : P.2 = 0 ∧ P.1 ≠ 0 ∧ (support P.1).card ≤ k then x ⟨P.1, h.2⟩ else 0

/-- Real-time evolution under the Hamiltonian `H(λ)` for time `τ` (§5.6, p.46: "the ability to evolve
under `e^(−iHt)`"), as a channel `ρ ↦ e^(−iH(λ)τ) ρ e^(iH(λ)τ)`.

**Formalization Note** The reused `conjugation l` is `ρ ↦ l ρ l†`; for purely imaginary `λ` the
operator `H(λ)` is Hermitian, so `(e^(−iHτ))† = e^(iHτ)`. -/
noncomputable def rtChannel {n k : ℕ} (lam : HIdx n k → ℂ) (τ : ℝ) : Super (Qubits n) (Qubits n) :=
  conjugation (NormedSpace.exp ((-((τ : ℂ) * Complex.I)) • hamOp lam))

/-- Access to copies of the Gibbs state (Theorem 5.18, p.52): the replacement channel
`ρ ↦ tr(ρ) · ρ_β`, with `ρ_β = e^(−βH(λ))/tr(e^(−βH(λ)))` the published thermal state
(`WolfAreaLaw.thermalState`). Applied to a prepared state it yields a fresh copy of `ρ_β`. -/
noncomputable def gibbsChannel {n k : ℕ} (β : ℝ) (lam : HIdx n k → ℂ) :
    Super (Qubits n) (Qubits n) := fun ij rs =>
  WolfAreaLaw.thermalState β (hamOp lam) ij.1 ij.2 * if rs.1 = rs.2 then 1 else 0

end LindbladStructLearn.Supplement


