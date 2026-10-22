-- Prove2me | Definitions.Def_WeingartenCalc_Fundamental_TensorPower
-- name    : WeingartenCalc_Fundamental_TensorPower
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:19.102288+00:00
-- url     : https://prove2.me/theorems/7554eb15-a937-4d11-baaf-b539426fe241
-- title:
--   Tensor-power matrices $U^{\otimes d}(g)$, invariant tensors $(H^{\otimes d})^G$, the Haar average $P$, and the Weingarten matrix $W=(A^*A)^{-1}$ (pp. 3–4)
-- statement:
--   This file fixes the objects of Section 2 of Collins, Matsumoto and Novak, *The Weingarten Calculus*.
--
--   Let $G$ be a group and $U : G \to \mathrm{U}(N)$ a group homomorphism into the $N\times N$ unitary matrices; think of $U(g)$ as a unitary operator on $H=\mathbb{C}^N$ written in the standard orthonormal basis $e_1,\dots,e_N$, so that its matrix elements are $U_{xy}(g)=\langle e_x, U(g)e_y\rangle$. Fix $d\in\mathbb{N}$ and write $\mathrm{Fun}(d,N)$ for the set of multi-indices $i : [d]\to[N]$. The tensor power $H^{\otimes d}$ has the orthonormal basis $e_i=e_{i(1)}\otimes\cdots\otimes e_{i(d)}$, $i\in\mathrm{Fun}(d,N)$, and is identified with the space of functions $\mathrm{Fun}(d,N)\to\mathbb{C}$.
--
--   1. **Tensor-power matrix.** The matrix of $U^{\otimes d}(g)$ in the basis $(e_i)$ is
--   $$U^{\otimes d}_{ij}(g)=\prod_{x=1}^{d} U_{i(x)j(x)}(g),\qquad i,j\in\mathrm{Fun}(d,N).$$
--   2. **Invariant tensors.** The subspace
--   $$(H^{\otimes d})^G=\{t\in H^{\otimes d} : U^{\otimes d}(g)\,t=t \text{ for all } g\in G\}.$$
--   3. **Haar average.** For a measure $\mu$ on $G$ (in the theorems: the Haar probability measure), the matrix $P=\int_G U^{\otimes d}(g)\,d\mu(g)$, the Bochner integral of the matrix-valued function $g\mapsto U^{\otimes d}(g)$.
--   4. **Coordinate matrix.** For vectors $a_1,\dots,a_m$ in a coordinate space $\mathbb{C}^n$, the $n\times m$ matrix $A=[\langle e_i,a_x\rangle]_{i,x}$ whose $x$-th column is $a_x$.
--   5. **Weingarten matrix.** $W=(A^*A)^{-1}$, the inverse of the Gram matrix $A^*A=[\langle a_x,a_y\rangle]_{x,y}$, where $A^*$ is the conjugate transpose.
--
--   These are the objects in terms of which the Fundamental Theorem of Weingarten Calculus (Theorem 2.1) and the steps of its proof are stated.
--
--   **Formalization Note** $H$ is $\mathbb{C}^N$ with its standard basis; a finite-dimensional Hilbert space with a specified orthonormal basis is the same thing after identifying it with $\mathbb{C}^N$ through that basis. Indices are 0-based (`Fin N`, `Fin d`), multi-indices are `Fin d → Fin N`, and tensors are functions `(Fin d → Fin N) → ℂ`. The invariant subspace is defined directly from the representation, not as the range of $P$. The matrix integral uses the entrywise sup norm on matrices (`Matrix.normedAddCommGroup`); in finite dimension the Bochner integral does not depend on the norm. Mathlib's matrix inverse returns $0$ on a singular matrix; every theorem using $W$ assumes the $a_x$ linearly independent, which makes the Gram matrix invertible.
-- source:
--   Collins, Matsumoto & Novak, The Weingarten Calculus, arXiv:2109.14890v1, pp. 3–4, Section 2 (eq. (2), the definition of P, (H⊗d)^G, A and W)

import Mathlib

namespace WeingartenCalc.Fundamental

open MeasureTheory Matrix

/-- Collins–Matsumoto–Novak, *The Weingarten Calculus*, arXiv:2109.14890v1, p. 3, (2):
the matrix of `U^{⊗d}(g)` in the product basis `e_i = e_{i(1)} ⊗ ⋯ ⊗ e_{i(d)}` of `H^{⊗d}`,
`U^{⊗d}_{ij}(g) = ∏_{x=1}^{d} U_{i(x) j(x)}(g)`, with `H = ℂ^N` and multi-indices
`i, j : Fin d → Fin N`. -/
def tensorPow {G : Type*} [Group G] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (d : ℕ)
    (g : G) : Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ :=
  Matrix.of fun i j => ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x)

/-- p. 4: the space of `G`-invariant tensors
`(H^{⊗d})^G = {t ∈ H^{⊗d} : U^{⊗d}(g) t = t for all g ∈ G}`. -/
def invariants {G : Type*} [Group G] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (d : ℕ) :
    Submodule ℂ ((Fin d → Fin N) → ℂ) where
  carrier := {t | ∀ g : G, (tensorPow U d g).mulVec t = t}
  add_mem' := by
    intro s t hs ht g
    rw [Matrix.mulVec_add, hs g, ht g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c t ht g
    rw [Matrix.mulVec_smul, ht g]

/-- p. 3: the averaging operator `P = ∫_G U^{⊗d}(g) dg`, the Bochner integral of the
matrix-valued function `g ↦ U^{⊗d}(g)` against `μ`. Matrices carry the entrywise sup norm
(`Matrix.normedAddCommGroup`) for this integral; in finite dimensions every norm gives the same
integral. -/
noncomputable def averagingOperator {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)
    {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (d : ℕ) :
    Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ :=
  letI : NormedAddCommGroup (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) :=
    Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) := Matrix.normedSpace
  ∫ g, tensorPow U d g ∂μ

/-- p. 4: the `N^d × m` matrix `A = [⟨e_i, a_x⟩]` whose columns are the coordinates of the
vectors `a_1, …, a_m`; with `H^{⊗d} = ℂ^{Fin d → Fin N}` and its standard basis,
`⟨e_i, a_x⟩ = a_x(i)`. -/
def coordMatrix {n : Type*} {m : ℕ} (a : Fin m → (n → ℂ)) : Matrix n (Fin m) ℂ :=
  Matrix.of fun i x => a x i

/-- p. 4: the Weingarten matrix `W = (A^* A)^{-1}`, the inverse of the Gram matrix
`A^* A = [⟨a_x, a_y⟩]` (Mathlib's `Matrix.inv`, which returns `0` on a singular matrix). -/
noncomputable def weingartenMatrix {n : Type*} [Fintype n] {m : ℕ} (a : Fin m → (n → ℂ)) :
    Matrix (Fin m) (Fin m) ℂ :=
  ((coordMatrix a)ᴴ * coordMatrix a)⁻¹

end WeingartenCalc.Fundamental


