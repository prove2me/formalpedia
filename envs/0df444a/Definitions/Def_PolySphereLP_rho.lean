-- Prove2me | Definitions.Def_PolySphereLP_rho
-- name    : PolySphereLP_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:28.871205+00:00
-- url     : https://prove2.me/theorems/3e5830cb-9ec8-4fe7-a49e-f43ed64b2779
-- title:
--   The rotation action $\rho(O)G(x)=G(O^{-1}x)$
-- statement:
--   For a real $n\times n$ matrix $O$ and a complex polynomial $G$,
--   $$(\rho(O)G)(x)=G(O^{-1}x),$$
--   the polynomial obtained by substituting $x_i\mapsto\sum_j(O^{-1})_{ij}x_j$.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Theorem 2.2, p.12

import Mathlib

namespace PolySphereLP

/-- **The rotation action `ρ_{n,k}(O)G(x) = G(O⁻¹x)`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Theorem 2.2, p.12:
`(ρ_{n,k}(O)G)(x) =def G(O⁻¹x)`.

`rho O G` substitutes `xᵢ ↦ ∑ⱼ (O⁻¹)ᵢⱼ xⱼ` in the complex polynomial `G`.

**Formalization Note.** A polynomial substitution, so `ρ(O)G` is again a polynomial; `O⁻¹` is the
matrix inverse (`= Oᵀ` for orthogonal `O`). -/
noncomputable def rho {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (G : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval
    (fun i => ∑ j, MvPolynomial.C (((O⁻¹) i j : ℝ) : ℂ) * MvPolynomial.X j) G

end PolySphereLP


