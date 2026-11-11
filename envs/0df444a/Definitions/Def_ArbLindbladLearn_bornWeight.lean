-- Prove2me | Definitions.Def_ArbLindbladLearn_bornWeight
-- name    : ArbLindbladLearn_bornWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:28.072428+00:00
-- url     : https://prove2.me/theorems/5a4daf5b-aa6b-4dfd-b551-e2dda1d33d1c
-- title:
--   Born weight of an experiment outcome
-- statement:
--   For circuits $C_1,C_2$ with unitaries $U_1,U_2$ and a channel $\Phi$ (in the goal $\Phi=e^{t\mathcal L}$), the probability of the outcome $b\in\{0,1\}^n$ is
--   $$\mathrm{Re}\,\langle b|\,U_2\,\Phi\big(U_1|0^n\rangle\langle0^n|U_1^\dagger\big)\,U_2^\dagger\,|b\rangle .$$
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), access model, §1.1, p.2

import Mathlib
import Definitions.Def_ArbLindbladLearn_Gate
import Definitions.Def_ArbLindbladLearn_basisVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The Born weight of outcome `b ∈ {0,1}ⁿ` of one experiment (access model, §1.1,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.2): prepare `U₁|0ⁿ⟩`, apply the channel `Φ` (in the goal,
`Φ = e^{tℒ}`), apply `U₂`, measure in the computational basis:
`Re ⟨b| U₂ Φ(U₁|0ⁿ⟩⟨0ⁿ|U₁†) U₂† |b⟩`, with `Uₖ = circuitU Cₖ`.

**Formalization Note** For a quantum channel this is a probability vector over `b`; the real part
is taken because the expression is real for Hermiticity-preserving `Φ`. -/
def bornWeight {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (C₁ C₂ : List (Gate n))
    (b : Qubits n) : ℝ :=
  ((circuitU C₂ * applySuper Φ (circuitU C₁ * zeroProj n * (circuitU C₁)ᴴ) *
    (circuitU C₂)ᴴ) b b).re

end ArbLindbladLearn


