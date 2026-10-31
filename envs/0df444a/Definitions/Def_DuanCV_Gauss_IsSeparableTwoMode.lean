-- Prove2me | Definitions.Def_DuanCV_Gauss_IsSeparableTwoMode
-- name    : DuanCV_Gauss_IsSeparableTwoMode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:39.736494+00:00
-- url     : https://prove2.me/theorems/757bf039-ddb4-4f5c-b498-dda7326ba72c
-- title:
--   Separability of a two-mode state: membership in the closed convex hull of product states
-- statement:
--   Consider two bosonic modes, with joint Hilbert space $\ell^2(\mathbb N\times\mathbb N)$. A density operator $\rho$ of the two modes is **separable** when it lies in the trace-norm closed convex hull of the product states $\rho_1\otimes\rho_2$, where mode 1 is the first tensor factor.
--
--   The paper writes this as $\rho=\sum_i p_i\,\rho_{i1}\otimes\rho_{i2}$ with $p_i\ge 0$, $\sum_i p_i=1$ and normalized $\rho_{i1},\rho_{i2}$. The closed hull contains every finite, countable or integral mixture of product states, including the mixtures of product coherent states that end the proof of Theorem 2.
--
--   **Formalization Note** The kernel is indexed by `Fin 2 → ℕ` and is relabelled to `ℕ × ℕ` by $f\mapsto(f(0),f(1))$ before the published definition `Dependency50.P33.IsSeparable` is applied.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eq. (1), p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19

open QAlgorithms.Papers.Independent.Claimed50.P19 (DensityKernel)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsSeparable)

namespace DuanCV.Gauss

/-- **Separability of a two-mode kernel.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eq. (1), p. 1.

A kernel `ρ` on the two-mode Fock index `Fin 2 → ℕ` is separable when, after relabelling the index
as `ℕ × ℕ` with mode 1 as the first tensor factor, it lies in the trace-norm closed convex hull of
the product states (`Dependency50.P33.IsSeparable`, Holevo–Shirokov–Werner, Definition 1).

**Formalization Note.** Eq. (1) writes `ρ = ∑ᵢ pᵢ ρᵢ₁ ⊗ ρᵢ₂` and leaves the index range open. The
paper's own proof of Theorem 2 concludes separability from the continuous mixture (19), so the
definition is the closed hull, which contains every finite, countable and integral mixture of
product states. `finTwoArrowEquiv ℕ` is `f ↦ (f 0, f 1)`, so index `0` is mode 1. -/
def IsSeparableTwoMode (ρ : DensityKernel 2) : Prop :=
  IsSeparable (ρ.submatrix (finTwoArrowEquiv ℕ).symm (finTwoArrowEquiv ℕ).symm)

end DuanCV.Gauss


