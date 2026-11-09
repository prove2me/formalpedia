-- Prove2me | Definitions.Def_DepthOneQExp_permToMatrix
-- name    : DepthOneQExp_permToMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:43:55.175089+00:00
-- url     : https://prove2.me/theorems/94805262-ae3e-44ef-bd95-3adefdb5dd4a
-- title:
--   Permutation matrix $|x\rangle \mapsto |\sigma x\rangle$
-- statement:
--   For a permutation $\sigma$ of a finite set of basis labels, $P_\sigma$ is the matrix with
--   $$
--   P_\sigma\,|x\rangle = |\sigma x\rangle, \qquad (P_\sigma)_{y,x} = \begin{cases}1 & y=\sigma x,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   This is how the paper turns a permutation of bit strings into a unitary: $\Gamma(g)|x\rangle = |g\cdot x\rangle$ (Eq. (2.8)), and elements of the CNOT group $G_n\le \mathrm{Sym}(2^n)$ are used as matrices. The map $\sigma\mapsto P_\sigma$ is multiplicative, $P_{\sigma\tau}=P_\sigma P_\tau$, and every $P_\sigma$ is unitary; both facts are proved in the module.
--
--   **Formalization Note** This is the transpose of Mathlib's `Equiv.Perm.permMatrix`, which represents $\sigma^{-1}$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.8), p.7

import Mathlib

namespace DepthOneQExp

/-- The permutation matrix of a permutation `σ` of a finite basis, acting as `|x⟩ ↦ |σ x⟩`
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eq. (2.8), p.7: "Γ(g)·|x⟩ =
|g·x⟩"): the entry in row `y` and column `x` is `1` if `y = σ x` and `0` otherwise.

**Formalization Note** This is *not* Mathlib's `Equiv.Perm.permMatrix σ`, whose entry `(i, j)` is
`1` iff `σ i = j` (it represents `σ⁻¹`). With the convention here the map is multiplicative
(`permToMatrix_mul`) and lands in the unitary group (`permToMatrix_mem_unitaryGroup`). -/
def permToMatrix {α : Type} [DecidableEq α] (σ : Equiv.Perm α) : Matrix α α ℂ :=
  fun y x => if y = σ x then 1 else 0

theorem permToMatrix_mul {α : Type} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    permToMatrix (σ * τ) = permToMatrix σ * permToMatrix τ := by
  ext y x
  simp only [permToMatrix, Matrix.mul_apply, Equiv.Perm.mul_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : y = σ (τ x) <;> simp [h]

theorem permToMatrix_one {α : Type} [DecidableEq α] :
    permToMatrix (1 : Equiv.Perm α) = 1 := by
  ext y x
  by_cases h : y = x <;> simp [permToMatrix, Matrix.one_apply, h]

theorem permToMatrix_mem_unitaryGroup {α : Type} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : permToMatrix σ ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext y x
  simp only [Matrix.mul_apply, Matrix.star_apply, permToMatrix, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ y)]
  · by_cases h : y = x
    · subst h; simp
    · have : σ y ≠ σ x := fun e => h (σ.injective e)
      simp [h, this]
  · intro b _ hb
    have : ¬ b = σ y := hb
    simp [this]
  · simp

end DepthOneQExp


