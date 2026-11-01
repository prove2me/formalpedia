-- Prove2me | Definitions.Def_PSDPolyApprox_shiftedDensity
-- name    : PSDPolyApprox_shiftedDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:53.141158+00:00
-- url     : https://prove2.me/theorems/b1b8413a-c7cd-460a-9498-aa5cef5ef39c
-- title:
--   The translate $\mathcal D-A$, flattened to $\mathbb R^{n\times n}$
-- statement:
--   For an $n\times n$ real matrix $A$, the translate
--   $$
--   \mathcal D-A=\{X-A : X\in\mathcal D\}
--   $$
--   of the set of density matrices, viewed as a subset of $\mathbb R^{n\times n}$. Theorem 1 sandwiches a polytope $P$ between $(1-\epsilon)(\mathcal D-A)$ and $\mathcal D-A$.
--
--   **Formalization Note** Polytopes and extension complexity are defined on coordinate spaces $\mathbb R^\iota$, so a matrix is flattened to its vector of entries ($\iota=\{1..n\}\times\{1..n\}$, Mathlib's `Matrix.vec`). This is a linear isomorphism carrying the trace inner product $\operatorname{Tr}(X^{\mathsf T}Y)$ to the dot product. The scaled set $(1-\epsilon)(\mathcal D-A)$ is the pointwise scalar multiple of this set.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §1, p.1 and Theorem 1, p.2

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices

namespace PSDPolyApprox

/-- **The translate `D − A`, flattened to a vector.**
Fawzi, arXiv:1811.09649v1, §1, p.1 and Theorem 1, p.2: the sets `(1 − ǫ)(D − A) ⊂ P ⊂ D − A`,
where `D − A = {X − A : X ∈ D}`.

`shiftedDensity n A` is the image of `D − A = {X − A | X ∈ densityMatrices n}` under the
flattening `Matrix.vec : Matrix (Fin n) (Fin n) ℝ → (Fin n × Fin n → ℝ)`.

**Formalization Note.** Polytopes and extension complexity (the reused
`ExtensionComplexity.TSP` definitions) live on `ι → ℝ`; here `ι = Fin n × Fin n` and
`Matrix.vec A (j, i) = A i j` is a linear isomorphism, which carries the Frobenius inner product
`Tr(XᵀY)` to the dot product. The scaled set `(1 − ǫ)(D − A)` is the pointwise scalar multiple
`(1 - ε) • shiftedDensity n A` (`vec` is linear). -/
def shiftedDensity (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n × Fin n → ℝ) :=
  Matrix.vec '' ((fun X => X - A) '' densityMatrices n)

end PSDPolyApprox


