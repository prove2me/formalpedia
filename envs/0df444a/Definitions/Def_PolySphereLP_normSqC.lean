-- Prove2me | Definitions.Def_PolySphereLP_normSqC
-- name    : PolySphereLP_normSqC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:15.141819+00:00
-- url     : https://prove2.me/theorems/33acec57-5b90-4d67-82bc-fad2084925cc
-- title:
--   The quadratic polynomial $x_1^2+\cdots+x_n^2$ over $\mathbb C$
-- statement:
--   The polynomial $x_1^2+\cdots+x_n^2\in\mathbb C[x_1,\dots,x_n]$. On real points it is $\|x\|^2$; on complex points $z\in\mathbb C^n$ it is $z^{\top}z$, with no complex conjugation, so it vanishes on the complex null cone $\{z: z^\top z=0\}$. It is the factor multiplying the remainder in the Fischer decomposition (16).
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (16), p.10; proof of Lemma A.4, p.29

import Mathlib

namespace PolySphereLP

/-- **The quadratic polynomial `x₁² + ⋯ + xₙ²` over `ℂ`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (16), p.10 and proof of Lemma A.4,
p.29: "with ‖x‖² replaced by the quadratic polynomial x₁² + ⋯ + xₙ²".

**Formalization Note.** No complex conjugation: on `ℂⁿ` this is `zᵀz`, which vanishes on the complex
null cone. -/
noncomputable def normSqC (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∑ i, MvPolynomial.X i ^ 2

end PolySphereLP


