-- Prove2me | Definitions.Def_ArbLindbladLearn_chiCoeff
-- name    : ArbLindbladLearn_chiCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:42.460808+00:00
-- url     : https://prove2.me/theorems/c9c0b9c8-8808-4a63-a1ca-e084aa426676
-- title:
--   The $\chi$-matrix of a superoperator
-- statement:
--   Every linear map on $n$-qubit operators has a unique expansion in the left–right Pauli basis
--   $$\mathcal N(\rho)=\sum_{a,b}\chi_{ab}\,P_a\rho P_b ,$$
--   over all labels including the identity. Applied to $\mathcal N=\mathcal L$ this is eq. (13); applied to $e^{t\mathcal L}$ it gives $\chi_{ab}(t)$.
--
--   **Formalization Note** The maps $X\mapsto P_aXP_b$ form an orthogonal basis of the superoperator space, each of squared Hilbert–Schmidt norm $d^2=4^n$; $\chi_{ab}$ is the projection coefficient $\langle P_a\cdot P_b,\mathcal N\rangle/d^2$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §3.1, eq. (13), p.18

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The `χ`-matrix of a superoperator (§3.1, eq. (13), Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.18): the
coefficients of the unique expansion `𝒩(ρ) = Σ_{a,b} χ_ab P_a ρ P_b` over all Pauli labels,
including the identity.

**Formalization Note** The maps `X ↦ P_a X P_b` (`leftRight (P a) (P b)`) are orthogonal for the
Hilbert–Schmidt inner product of superoperator matrices, each with squared norm `d² = 4ⁿ`, and
there are `d⁴` of them, so they form an orthogonal basis; `χ_ab` is the corresponding projection
coefficient `⟨P_a·P_b, 𝒩⟩ / d²`. Applied to `𝒩 = ℒ` this is eq. (13), applied to `e^{tℒ}` it
is `χ_ab(t)`. -/
def chiCoeff {n : ℕ} (g : Super (Qubits n) (Qubits n)) (a b : Pauli n) : ℂ :=
  (∑ ij, ∑ rs, star (leftRight (pauliMatrix a) (pauliMatrix b) ij rs) * g ij rs) /
    ((2 : ℂ) ^ n) ^ 2

end ArbLindbladLearn


