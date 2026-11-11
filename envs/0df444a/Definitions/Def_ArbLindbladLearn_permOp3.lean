-- Prove2me | Definitions.Def_ArbLindbladLearn_permOp3
-- name    : ArbLindbladLearn_permOp3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:45.610186+00:00
-- url     : https://prove2.me/theorems/d183464d-45af-4a75-835c-c178454c6e32
-- title:
--   SWAP and the permutation operators $W_\pi$ on $\mathcal H^{\otimes3}$
-- statement:
--   SWAP exchanges the two factors of $\mathcal H\otimes\mathcal H$, and for $\pi\in S_3$ the operator $W_\pi$ permutes the three factors of $\mathcal H^{\otimes3}$: $W_\pi|x_0x_1x_2\rangle=|y\rangle$ with $y_{\pi(k)}=x_k$.
--
--   **Formalization Note** Fact 4.3 uses only $\sum_{\pi\in S_3}W_\pi$, which does not depend on the convention $\pi$ versus $\pi^{-1}$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Fact 4.3, p.28

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The operator `SWAP` exchanging the two factors of `ℋ ⊗ ℋ` (Fact 4.3,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.28): `⟨(x₁,x₂)|SWAP|(y₁,y₂)⟩ = 1[x₁ = y₂ ∧ x₂ = y₁]`. -/
def swapOp (n : ℕ) : Op (Qubits n × Qubits n) :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- The three tensor factors of an index of `(ℋ ⊗ ℋ) ⊗ ℋ`. -/
def triple {n : ℕ} (x : (Qubits n × Qubits n) × Qubits n) : Fin 3 → Qubits n :=
  ![x.1.1, x.1.2, x.2]

/-- The operator `W_π` permuting the three factors of `ℋ^{⊗3}` according to `π ∈ S₃` (Fact 4.3,
p.28): `W_π |x₀ x₁ x₂⟩ = |y⟩` with `y_{π k} = x_k`.

**Formalization Note** Fact 4.3 uses only `Σ_{π ∈ S₃} W_π`, which is the same for the convention
`π` or `π⁻¹`. -/
def permOp3 (n : ℕ) (π : Equiv.Perm (Fin 3)) : Op ((Qubits n × Qubits n) × Qubits n) :=
  fun y x => if ∀ k : Fin 3, triple y (π k) = triple x k then 1 else 0

end ArbLindbladLearn


