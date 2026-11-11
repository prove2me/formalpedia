-- Prove2me | Definitions.Def_ArbLindbladLearn_Stab
-- name    : ArbLindbladLearn_Stab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:20.036812+00:00
-- url     : https://prove2.me/theorems/9f78c104-e4c4-4b29-af59-f7e838e5925e
-- title:
--   Clifford unitaries, stabilizer states $\mathrm{Stab}_n$, uniform stabilizer average
-- statement:
--   A **Clifford unitary** is a unitary $C$ that maps Pauli operators to Pauli operators up to phase under conjugation: $CP_aC^\dagger=\omega P_b$. The set of pure stabilizer-state projectors is
--   $$\mathrm{Stab}_n=\{C|0^n\rangle\langle0^n|C^\dagger: C\in\mathrm{Cl}_n\},$$
--   and `stabAvg F` is the expectation of $F(\varphi)$ for $\varphi$ uniform on $\mathrm{Stab}_n$.
--
--   **Formalization Note** $\mathrm{Stab}_n$ is finite and nonempty (a fact, not part of the definition); the average is $|\mathrm{Stab}_n|^{-1}\sum_{\varphi\in\mathrm{Stab}_n}F(\varphi)$, written with `Set.ncard` and a finite sum.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §4.2, p.27; Fact 4.3, p.28

import Mathlib
import Definitions.Def_ArbLindbladLearn_basisVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- A Clifford unitary (§4.2, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.27): a unitary `U` mapping Pauli
operators to Pauli operators up to phase under conjugation, `U P_a U† = ω P_b`. -/
def IsClifford {n : ℕ} (U : Op (Qubits n)) : Prop :=
  U ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
    ∀ a : Pauli n, ∃ (b : Pauli n) (ω : ℂ), U * pauliMatrix a * Uᴴ = ω • pauliMatrix b

/-- The set `Stab_n = {C|0ⁿ⟩⟨0ⁿ|C† : C ∈ Cl_n}` of pure `n`-qubit stabilizer-state projectors
(§4.2, p.27). -/
def Stab (n : ℕ) : Set (Op (Qubits n)) :=
  {φ | ∃ U : Op (Qubits n), IsClifford U ∧ φ = U * zeroProj n * Uᴴ}

/-- The expectation `E_φ[F(φ)]` over a uniformly random `φ ∈ Stab_n` (Fact 4.3, p.28).

**Formalization Note** `Stab_n` is a finite nonempty set (a stabilizer state is determined by
its signed stabilizer group, a subgroup of the finite Pauli group); this is a fact, not part of
the definition. The average is `|Stab_n|⁻¹ Σ_{φ ∈ Stab_n} F(φ)`, written with `Set.ncard` and a
finite sum `∑ᶠ`. -/
def stabAvg {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℂ M] (F : Op (Qubits n) → M) : M :=
  (((Stab n).ncard : ℂ)⁻¹) • ∑ᶠ φ ∈ Stab n, F φ

end ArbLindbladLearn


