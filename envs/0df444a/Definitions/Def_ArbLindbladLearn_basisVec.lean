-- Prove2me | Definitions.Def_ArbLindbladLearn_basisVec
-- name    : ArbLindbladLearn_basisVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:53.061788+00:00
-- url     : https://prove2.me/theorems/5c0f0fc1-81f0-4d9f-b7d3-6d772f090efd
-- title:
--   Computational basis vectors, $|0^n\rangle\langle0^n|$, bitwise xor, quadratic form
-- statement:
--   Helpers for the experiments: the computational basis vector $|u\rangle$, $u\in\{0,1\}^n$; the projector $|0^n\rangle\langle0^n|$; the bitwise sum $u\oplus v$; and the quadratic form $\langle v|M|v\rangle$, which is the Born probability of outcome $v$ for a state $M$ and a unit vector $v$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithm 1, p.23; §4.2, p.27

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The computational basis vector `|u⟩`, `u ∈ {0,1}ⁿ` (Algorithm 1, line 6,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.23). -/
def basisVec {n : ℕ} (u : Qubits n) : Qubits n → ℂ := fun x => if x = u then 1 else 0

/-- The projector `|0ⁿ⟩⟨0ⁿ|` (§4.2, p.27). -/
def zeroProj (n : ℕ) : Op (Qubits n) := outer (basisVec fun _ => false) (basisVec fun _ => false)

/-- Bitwise sum `u ⊕ v` of bit strings (§2.1, p.11). -/
def xorBits {n : ℕ} (u v : Qubits n) : Qubits n := fun i => xor (u i) (v i)

/-- The quadratic form `⟨v| M |v⟩`; for a density operator and a unit vector it is the Born
probability of the outcome `v`. -/
def quadForm {n : ℕ} (v : Qubits n → ℂ) (M : Op (Qubits n)) : ℂ := star v ⬝ᵥ (M *ᵥ v)

end ArbLindbladLearn


