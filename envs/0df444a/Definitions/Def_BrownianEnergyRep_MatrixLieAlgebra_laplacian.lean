-- Prove2me | Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra_laplacian
-- name    : BrownianEnergyRep_MatrixLieAlgebra_laplacian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:28.555463+00:00
-- url     : https://prove2.me/theorems/65541be3-6511-4085-b949-d5a4c499bb0a
-- title:
--   The left Laplacian $\Delta=\sum_{A\in\mathfrak g_0}\widetilde A^2$ on $G$
-- statement:
--   For $A\in\mathfrak g$, the left-invariant vector field $\widetilde A$ acts on a function $f$ on $G$ by
--   $$
--   \widetilde Af(x)=\frac{d}{dt}\Big|_{0} f\big(xe^{tA}\big).
--   $$
--   For an orthonormal basis $\mathfrak g_0$ of $\mathfrak g$, the left Laplacian is
--   $$
--   \Delta=\sum_{A\in\mathfrak g_0}\widetilde A^2 .
--   $$
--   It is the generator (up to the factor $\tfrac12$) of Brownian motion on $G$.
--
--   **Formalization Note** The module also defines $e^{A}$ as an element of $G$. The basis used is `stdOrthonormalBasis`; $\Delta$ does not depend on the choice.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, §2.1, p.2

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The exponential `e^A ∈ G` of `A = incl a ∈ 𝔤` (arXiv:1511.07378v1, p.2). It is the unique element of `G`
whose matrix is `exp (incl a)`. -/
noncomputable def MatrixLieAlgebra.expG {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E) (a : E) : ↥G :=
  ⟨Classical.choose ((L.mem_range_iff (L.incl a)).1 ⟨a, rfl⟩ 1),
    (Classical.choose_spec ((L.mem_range_iff (L.incl a)).1 ⟨a, rfl⟩ 1)).1⟩

/-- The left-invariant vector field `Ã` of `A = incl a` acting on a function,
`Ãf(x) = d/dt|₀ f(x e^{tA})` (arXiv:1511.07378v1, §2.1, p.2 and p.8). -/
noncomputable def MatrixLieAlgebra.leftDeriv {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E) (a : E)
    (f : ↥G → ℝ) (x : ↥G) : ℝ :=
  deriv (fun t : ℝ => f (x * L.expG (t • a))) 0

/-- The left Laplacian `Δ = Σ_{A ∈ 𝔤₀} Ã²` for an orthonormal basis `𝔤₀` of `𝔤`
(arXiv:1511.07378v1, §2.1, p.2).

**Formalization Note** The basis is `stdOrthonormalBasis ℝ E`; `Δ` does not depend on it. -/
noncomputable def MatrixLieAlgebra.laplacian {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (f : ↥G → ℝ) (x : ↥G) : ℝ :=
  ∑ i, L.leftDeriv (stdOrthonormalBasis ℝ E i) (L.leftDeriv (stdOrthonormalBasis ℝ E i) f) x

end BrownianEnergyRep


