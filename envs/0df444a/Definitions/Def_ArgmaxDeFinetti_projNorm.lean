-- Prove2me | Definitions.Def_ArgmaxDeFinetti_projNorm
-- name    : ArgmaxDeFinetti_projNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:03.326549+00:00
-- url     : https://prove2.me/theorems/09c8069f-cbab-4b2b-9a4e-068276747d77
-- title:
--   Projective tensor norm $\|z\|_\pi$
-- statement:
--   For $z\in\mathcal X\otimes\mathcal Y$,
--   $$
--   \|z\|_\pi=\inf\Big\{\sum_j|a_j|:\ z=\sum_j a_j\,x_j\otimes y_j,\ \|x_j\|=\|y_j\|=1\Big\}.
--   $$
--
--   **Formalization Note** The infimum is over decompositions of every finite length (length $0$ for $z=0$), with Euclidean unit vectors.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.21, eq. (2.14)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_injNorm

open Matrix

namespace ArgmaxDeFinetti

/-- The projective tensor norm
`∥z∥_π = inf { Σ_j |a_j| : z = Σ_j a_j x_j ⊗ y_j, ∥x_j∥ = ∥y_j∥ = 1 }` of `z ∈ X ⊗ Y`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (2.14), p.21.

**Formalization Note** The infimum runs over decompositions of every finite length `k` (including `k = 0` for
`z = 0`); norms are Euclidean (`vnorm`). The set is nonempty and bounded below by `0`. -/
noncomputable def projNorm {ι κ : Type} [Fintype ι] [Fintype κ] (z : ι × κ → ℂ) : ℝ :=
  sInf {r | ∃ (k : ℕ) (a : Fin k → ℂ) (x : Fin k → ι → ℂ) (y : Fin k → κ → ℂ),
    (∀ j, vnorm (x j) = 1 ∧ vnorm (y j) = 1) ∧ z = ∑ j, a j • prodVec (x j) (y j) ∧
      r = ∑ j, ‖a j‖}

end ArgmaxDeFinetti


