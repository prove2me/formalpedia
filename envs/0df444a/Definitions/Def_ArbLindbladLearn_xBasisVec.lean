-- Prove2me | Definitions.Def_ArbLindbladLearn_xBasisVec
-- name    : ArbLindbladLearn_xBasisVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:13.932889+00:00
-- url     : https://prove2.me/theorems/05f98b60-57eb-4dbd-88c7-1b157a774d3c
-- title:
--   $X$-basis states $|u\rangle_X=H^{\otimes n}|u\rangle$
-- statement:
--   The $n$-qubit Hadamard has entries $\langle x|H^{\otimes n}|y\rangle=(-1)^{x\cdot y}/\sqrt{2^n}$, and the $X$-basis state of $u\in\{0,1\}^n$ is $|u\rangle_X=H^{\otimes n}|u\rangle$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.7, p.23

import Mathlib
import Definitions.Def_ArbLindbladLearn_basisVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The `n`-qubit Hadamard `H^{⊗n}`, `⟨x|H^{⊗n}|y⟩ = (−1)^{x·y}/√(2ⁿ)` (Lemma 3.7,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.23). -/
def hadamardAll (n : ℕ) : Op (Qubits n) := fun x y =>
  (-1 : ℂ) ^ (Finset.univ.filter fun i => x i = true ∧ y i = true).card /
    (Real.sqrt ((2 : ℝ) ^ n) : ℂ)

/-- The `X`-basis state `|u⟩_X = H^{⊗n}|u⟩` (Lemma 3.7, p.23). -/
def xBasisVec {n : ℕ} (u : Qubits n) : Qubits n → ℂ := hadamardAll n *ᵥ basisVec u

end ArbLindbladLearn


