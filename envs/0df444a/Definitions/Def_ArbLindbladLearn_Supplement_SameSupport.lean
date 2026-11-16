-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_SameSupport
-- name    : ArbLindbladLearn_Supplement_SameSupport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:18:31.53021+00:00
-- url     : https://prove2.me/theorems/8cafb4c8-1d52-44aa-bb7e-67ee2382dd48
-- title:
--   Two Lindbladians with identical Hamiltonian and dissipative supports
-- statement:
--   Two $n$-qubit Lindbladians with coefficients $(h,\gamma)$ and $(h',\gamma')$ have **identical Hamiltonian and dissipative supports** if $\mathcal S_H=\mathcal S'_H$ and $\mathcal S_D=\mathcal S'_D$ (Definition 2.7), i.e.
--   $$h_a\ne0\iff h'_a\ne0\quad(a\ne0),\qquad\gamma_{ab}\ne0\iff\gamma'_{ab}\ne0\quad(a,b\ne0).$$
--
--   The hard instances of Theorems 5.7 and 5.8 have this property, which is why the lower bounds hold even with knowledge of the support.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.7, p.14; Theorems 5.7–5.8, pp.45–46

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- Two Lindbladians have identical Hamiltonian and dissipative supports (Definition 2.7, p.14;
Theorems 5.7–5.8, pp.45–46: "The hard instances … have identical Hamiltonian and dissipative
supports"; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)): `𝒮_H` and `𝒮_D` agree, i.e. `h_a ≠ 0 ↔ h'_a ≠ 0` for every `a ≠ 0` and
`γ_ab ≠ 0 ↔ γ'_ab ≠ 0` for all `a, b ≠ 0`. -/
def SameSupport {n : ℕ} (c₁ c₂ : Coeffs n) : Prop :=
  (∀ a : Pauli n, a ≠ 0 → (c₁.h a ≠ 0 ↔ c₂.h a ≠ 0)) ∧
  (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → (c₁.γ a b ≠ 0 ↔ c₂.γ a b ≠ 0))

end ArbLindbladLearn.Supplement


