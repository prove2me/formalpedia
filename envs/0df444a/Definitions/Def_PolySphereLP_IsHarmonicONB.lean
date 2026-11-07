-- Prove2me | Definitions.Def_PolySphereLP_IsHarmonicONB
-- name    : PolySphereLP_IsHarmonicONB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:22.371933+00:00
-- url     : https://prove2.me/theorems/91984c74-e387-4589-baa6-a4fa8cb1ce9b
-- title:
--   An $L^2(\sigma)$-orthonormal basis $Y_1,\dots,Y_h$ of $\mathcal H_{n,d}$
-- statement:
--   A family $Y_1,\dots,Y_h$ of real polynomials is an **$L^2(\sigma)$-orthonormal basis of $\mathcal H_{n,d}$** when
--   1. every $Y_i$ lies in $\mathcal H_{n,d}$;
--   2. $\int Y_iY_j\,d\sigma=\delta_{ij}$ for all $i,j$;
--   3. the $Y_i$ span $\mathcal H_{n,d}$.
--
--   Then $h=h_{n,d}$. The random model of the paper fixes any such basis.
--
--   **Formalization Note** The index set is $\{0,\dots,h-1\}$. Such bases exist (Gram–Schmidt on the finite-dimensional $\mathcal H_{n,d}$ with the positive-definite form $\int pq\,d\sigma$).
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §1.2, p.5; (14), p.10

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_harmonicSpace

namespace PolySphereLP

/-- **An `L²(σ)`-orthonormal basis `Y₁,…,Y_h` of `ℋ_{n,d}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §1.2, p.5 ("Choose any
`L²(σ)`-orthonormal basis `Y₁,…,Y_h`") and (14), p.10.

`IsHarmonicONB n d h Y` says: every `Yᵢ` lies in `ℋ_{n,d}`; `∫ Yᵢ Yⱼ dσ = δᵢⱼ`; and the `Yᵢ` span
`ℋ_{n,d}`.

**Formalization Note.** The index set is `Fin h`; orthonormality and spanning force
`h = dim ℋ_{n,d} = h_{n,d}`. The predicate is satisfiable: `ℋ_{n,d}` is finite-dimensional and the
`L²(σ)` form is positive definite on it, so Gram–Schmidt applies. -/
def IsHarmonicONB (n d h : ℕ) (Y : Fin h → MvPolynomial (Fin n) ℝ) : Prop :=
  (∀ i, Y i ∈ harmonicSpace n d) ∧
  (∀ i j, ∫ x, MvPolynomial.eval x (Y i) * MvPolynomial.eval x (Y j) ∂(SphereSOS.Rate.sigma n) =
    if i = j then 1 else 0) ∧
  harmonicSpace n d ≤ Submodule.span ℝ (Set.range Y)

end PolySphereLP


