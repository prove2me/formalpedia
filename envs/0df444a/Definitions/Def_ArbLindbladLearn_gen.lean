-- Prove2me | Definitions.Def_ArbLindbladLearn_gen
-- name    : ArbLindbladLearn_gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:41.680035+00:00
-- url     : https://prove2.me/theorems/f48e9630-159c-40e1-a085-9e6f2b2dce3a
-- title:
--   The Lindbladian generator $\mathcal L$ of eq. (8)
-- statement:
--   Given coefficients $(h,\gamma)$, the generator is the superoperator
--   $$\mathcal L(\rho)=\sum_{a\neq0}-\mathrm i\,h_a[P_a,\rho]+\sum_{a,b\neq0}\gamma_{ab}\Big(P_a\rho P_b-\tfrac12\{P_bP_a,\rho\}\Big),$$
--   where $[A,B]=AB-BA$ and $\{A,B\}=AB+BA$. The channel at time $t$ is $e^{t\mathcal L}$, the public `evolution (gen c) t`.
--
--   **Formalization Note** The superoperator is a matrix in matrix units; `leftRight A B` is the public map $X\mapsto AXB$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.6, eq. (8), p.14

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The Lindbladian generator of the coefficients `c` (Definition 2.6, eq. (8),
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.14):
`ℒ(ρ) = Σ_{a≠0} −i h_a [P_a, ρ] + Σ_{a,b≠0} γ_ab (P_a ρ P_b − ½ {P_b P_a, ρ})`,
as the matrix of a superoperator on `n` qubits.

**Formalization Note** `leftRight A B` is the public superoperator `X ↦ A X B`
(`(applySuper (leftRight A B) X) i j = Σ_{r,s} A i r X r s B s j`). The commutator is
`leftRight P 1 − leftRight 1 P` and the anticommutator `{Q, ρ}` is
`leftRight Q 1 + leftRight 1 Q`. The semigroup `e^{tℒ}` is the public `evolution (gen c) t`. -/
def gen {n : ℕ} (c : Coeffs n) : Super (Qubits n) (Qubits n) :=
  (∑ a ∈ Finset.univ.filter (fun a : Pauli n => a ≠ 0),
      (-(Complex.I * (c.h a : ℂ))) •
        (leftRight (pauliMatrix a) 1 - leftRight 1 (pauliMatrix a))) +
  ∑ a ∈ Finset.univ.filter (fun a : Pauli n => a ≠ 0),
    ∑ b ∈ Finset.univ.filter (fun b : Pauli n => b ≠ 0),
      c.γ a b • (leftRight (pauliMatrix a) (pauliMatrix b) -
        (1 / 2 : ℂ) • (leftRight (pauliMatrix b * pauliMatrix a) 1 +
          leftRight 1 (pauliMatrix b * pauliMatrix a)))

end ArbLindbladLearn


