-- Prove2me | Definitions.Def_RadGauss_Kernel_KernelClass
-- name    : RadGauss_Kernel_KernelClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:05:36.758986+00:00
-- url     : https://prove2.me/theorems/3927a8c2-f6f4-46bd-92ac-2f86abffb9d1
-- title:
--   §4.3 — kernels on a compact space and the class F of kernel expansions Σ α_i k(·, x_i) with Σ α_iα_j k(x_i, x_j) ≤ B²
-- statement:
--   Let $\mathcal X$ be a topological space.
--
--   1. A **kernel** $k : \mathcal X \times \mathcal X \to \mathbb R$ on $\mathcal X$ is a continuous function on a compact space $\mathcal X$ such that for every $m \in \mathbb N$ and all $x_1, \dots, x_m \in \mathcal X$ the Gram matrix $K$, $K_{ij} = k(x_i, x_j)$, is symmetric and positive semidefinite.
--   2. For a function $k$ and a real number $B$, the **class of kernel expansions** is
--   $$F = \Big\{\,x \mapsto \sum_{i=1}^m \alpha_i\, k(x, x_i) \;:\; m \in \mathbb N,\ x_i \in \mathcal X,\ \alpha_i \in \mathbb R,\ \sum_{i,j} \alpha_i \alpha_j\, k(x_i, x_j) \le B^2\Big\}.$$
--   The centres $x_i$ range over all of $\mathcal X$ (not only over a sample), may repeat, and $m = 0$ gives the zero function.
--
--   Kernel methods such as support vector machines output functions of this form, with the quadratic form $\alpha' K \alpha$ controlling the size of the expansion; this class is the subject of Lemma 22 and of the bound after it.
--
--   **Formalization Note** `IsKernel k` bundles compactness of $\mathcal X$, joint continuity of $(x, y) \mapsto k(x, y)$, and `Matrix.PosSemidef` of every Gram matrix indexed by `Fin m`; for a real matrix Mathlib's `PosSemidef` includes symmetry. The kernel is written curried, `k x y`.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 476 (PDF p. 14), §4.3 definition of a kernel; p. 477 (PDF p. 15), the class F

import Mathlib

namespace RadGauss.Kernel

/-- **Kernel** (Bartlett–Mendelson 2002, §4.3, p. 476): a kernel `k : 𝒳 × 𝒳 → ℝ` on a compact
space `𝒳` is a continuous function such that for every `m` and all `x_1, …, x_m ∈ 𝒳` the Gram
matrix `K_ij = k(x_i, x_j)` is symmetric and positive semidefinite. `k` is written curried;
continuity is joint continuity of `(x, y) ↦ k x y`. Mathlib's `Matrix.PosSemidef` of a real
matrix includes symmetry (`IsHermitian`). -/
structure IsKernel {X : Type*} [TopologicalSpace X] (k : X → X → ℝ) : Prop where
  compactSpace : CompactSpace X
  continuous : Continuous (Function.uncurry k)
  gram_posSemidef : ∀ (m : ℕ) (x : Fin m → X), (Matrix.of fun i j => k (x i) (x j)).PosSemidef

/-- **The class of kernel expansions** (§4.3, p. 477):
`F = {x ↦ Σ_{i=1}^m α_i k(x, x_i) : m ∈ ℕ, x_i ∈ 𝒳, Σ_{i,j} α_i α_j k(x_i, x_j) ≤ B²}`,
every finite expansion with centres `c_1, …, c_m` anywhere in `𝒳` (repetitions allowed, `m = 0`
gives the zero function) and real coefficients `α` with `α'Kα ≤ B²`. -/
def kernelClass {X : Type*} (k : X → X → ℝ) (B : ℝ) : Set (X → ℝ) :=
  {f | ∃ (m : ℕ) (c : Fin m → X) (α : Fin m → ℝ),
    ∑ i, ∑ j, α i * α j * k (c i) (c j) ≤ B ^ 2 ∧ f = fun x => ∑ i, α i * k x (c i)}

end RadGauss.Kernel


