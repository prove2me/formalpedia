-- Prove2me | Definitions.Def_ICSCompute_IsQuantumChannel
-- name    : ICSCompute_IsQuantumChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:17.980737+00:00
-- url     : https://prove2.me/theorems/f3be6ee2-295d-41b1-ab1c-05e0f7f39d75
-- title:
--   Quantum channel (completely positive, trace-preserving linear map)
-- statement:
--   Let $\mathcal C$ be a linear map from $\mathcal L(H_0)$ to $\mathcal L(H_1)$.
--
--   1. $\mathcal C$ is **completely positive** if for every additional register $Z$ and every positive semidefinite $X\in\mathcal L(H_0\otimes H_Z)$ the matrix $(\mathcal C\otimes \mathrm{id}_Z)(X)$ is positive semidefinite.
--   2. $\mathcal C$ is **trace preserving** if $\operatorname{Tr}\mathcal C(X) = \operatorname{Tr} X$ for every $X\in\mathcal L(H_0)$.
--
--   A **quantum channel** is a completely positive, trace-preserving linear map.
--
--   Channels are the local operations inserted into the feedback pairs and the objects a valid process must produce.
--
--   **Formalization Note** The reference register $Z$ ranges over all qubit registers $\mathcal S(m)$, $m\ge 0$, as the paper's registers are qubit spaces. $(\mathcal C\otimes\mathrm{id}_Z)(X)$ applies $\mathcal C$ to each block $X_{z z'}$ of $X = \sum_{z,z'} X_{zz'}\otimes|z\rangle\langle z'|$. Trace preservation is required on all matrices, as in Definition 3.12.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definitions 3.12–3.13, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ICSCompute

open QAlgorithms
open scoped ComplexOrder

/-- The map `C ⊗ id_Z` on `L(H₀ ⊗ H_Z)`: for `X = ∑_{z,z'} X_{z z'} ⊗ |z⟩⟨z'|` it returns
`∑_{z,z'} C(X_{z z'}) ⊗ |z⟩⟨z'|` (Shmueli, arXiv:2610.40573, Definition 3.12, p.16 (PDF p.18)).
Its `((k, z), (k', z'))` entry is the `(k, k')` entry of `C` applied to the block
`X_{z z'} = (X (i, z) (i', z'))_{i, i'}`. -/
def tensorId {ι κ Z : Type*} (C : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × Z) (ι × Z) ℂ) : Matrix (κ × Z) (κ × Z) ℂ :=
  Matrix.of fun a b => C (Matrix.of fun i i' => X (i, a.2) (i', b.2)) a.1 b.1

/-- **Quantum channel** (Shmueli, *What Can Be Computed with Indefinite Causal Structure?*,
arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definitions 3.12–3.13, p.16
(PDF p.18)).

A linear map `C ∈ L(L(H₀), L(H₁))` is **completely positive** if for every additional register
`Z` and every positive semidefinite `X ∈ L(H₀ ⊗ H_Z)` the matrix `(C ⊗ id_Z)(X)` is positive
semidefinite; it is **trace preserving** if `Tr C(X) = Tr X` for every `X ∈ L(H₀)`. A quantum
channel is a CPTP linear map.

**Formalization Note** The additional register `Z` ranges over all qubit registers
`S(m) = ℂ^{2^m}`, `m ∈ ℕ` (index type `Qubits m`, including `m = 0`), as in the paper, whose
registers are qubit spaces (§3, p.14). Trace preservation is required for every matrix, not only
for density matrices, exactly as in Definition 3.12. -/
def IsQuantumChannel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : Prop :=
  (∀ (m : ℕ) (X : Matrix (ι × Qubits m) (ι × Qubits m) ℂ), X.PosSemidef →
      (tensorId C X).PosSemidef) ∧
    ∀ X : Matrix ι ι ℂ, (C X).trace = X.trace

end ICSCompute


