-- Prove2me | Definitions.Def_ArbLindbladLearn_bellVec
-- name    : ArbLindbladLearn_bellVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:43.171038+00:00
-- url     : https://prove2.me/theorems/0ad42554-cda2-4dbb-a281-05a7d2edd814
-- title:
--   Bell vectors $|\Phi_A\rangle=(I\otimes A)|\Phi_0\rangle$ and matrix elements
-- statement:
--   With $d=2^n$ and the maximally entangled state $|\Phi_0\rangle=d^{-1/2}\sum_j|j\rangle|j\rangle$ on $\mathcal H\otimes\mathcal H$, the Bell vector of an operator $A$ is $|\Phi_A\rangle=(I\otimes A)|\Phi_0\rangle$; for a Pauli label, $|\Phi_a\rangle=(I\otimes P_a)|\Phi_0\rangle$. The helper `bellForm` is the matrix element $\langle u|J|v\rangle$.
--
--   **Formalization Note** The reference factor is first, as in the paper: the component of $|\Phi_A\rangle$ at $(r,s)$ is $A_{sr}/\sqrt d$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §2.4, p.15

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The Bell vector `|Φ_A⟩ = (I ⊗ A)|Φ₀⟩` of an operator `A` (§2.4, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.15), with `|Φ₀⟩ = d^{−1/2} Σ_j |j⟩|j⟩` and `d = 2ⁿ`.

**Formalization Note** Vectors on `ℋ ⊗ ℋ` are functions on `Qubits n × Qubits n` with the
**reference** factor first, as in the paper; the component at `(r, s)` is `A s r / √d`. For a
Pauli label, `|Φ_a⟩ = bellVec (pauliMatrix a)`. -/
def bellVec {n : ℕ} (A : Op (Qubits n)) : Qubits n × Qubits n → ℂ :=
  fun x => A x.2 x.1 / (Real.sqrt ((2 : ℝ) ^ n) : ℂ)

/-- The matrix element `⟨u| J |v⟩ = Σ_{x,y} conj(u x) J x y v y` on `ℋ ⊗ ℋ` (§2.4, p.15). -/
def bellForm {n : ℕ} (J : Op (Qubits n × Qubits n)) (u v : Qubits n × Qubits n → ℂ) : ℂ :=
  ∑ x, ∑ y, star (u x) * J x y * v y

end ArbLindbladLearn


