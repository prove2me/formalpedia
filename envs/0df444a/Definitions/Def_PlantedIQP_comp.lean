-- Prove2me | Definitions.Def_PlantedIQP_comp
-- name    : PlantedIQP_comp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:13.316578+00:00
-- url     : https://prove2.me/theorems/18d2c3d1-6415-482e-865d-2ecda0f10d97
-- title:
--   Composition $f\circ A$ with $A\in GL(n,\mathbb F_2)$
-- statement:
--   For a cubic polynomial $f$ and an invertible matrix $A\in GL(n,\mathbb F_2)$, the composition $f\circ A$ is the multilinear representative of the function
--
--   $$
--   x\longmapsto f(Ax).
--   $$
--
--   Because $x\mapsto f(Ax)$ has degree at most $3$ and vanishes at $x=0$, $f\circ A$ is again a cubic polynomial with constant term $0$, with $(f\circ A)(x)=f(Ax)$ for every $x$.
--
--   Composition with $GL(n,\mathbb F_2)$ is how independent spaces are defined (Definition 1) and how the planted law hides its subspace (Section 2.3).
--
--   **Formalization Note** $GL(n,\mathbb F_2)$ is `Matrix.GeneralLinearGroup (Fin n) (ZMod 2)`; the record of $f\circ A$ is read off by Möbius inversion of $x\mapsto f(Ax)$.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), p.5 and Section 2.1, p.13

import Mathlib
import Definitions.Def_PlantedIQP_mobiusCoeff

set_option autoImplicit false

namespace PlantedIQP

/-!
# Composition of a cubic polynomial with an invertible linear map

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), p.5: "the polynomials g ◦ A defined as
g ◦ A(x) = g(Ax) for A ∈ GL(n, 𝔽₂)"; Section 2.1, p.13: "we reduce compositions such as f ◦ A back
to this representative".

**Formalization Note.**
* `GL(n, 𝔽₂)` is `Matrix.GeneralLinearGroup (Fin n) (ZMod 2)` and `A x` is the matrix-vector
  product `(A : Matrix _ _ _) *ᵥ x`.
* `f.comp A` is the record of the multilinear representative of `x ↦ f(Ax)`, read off by Möbius
  inversion (`CubicPoly.ofFun`). The function `x ↦ f(Ax)` has degree at most 3 and vanishes at
  `x = 0` (since `A0 = 0`), so the record has the same evaluations: `(f.comp A).eval x = f.eval (A x)`.
-/

/-- `f ◦ A`: the multilinear representative of `x ↦ f(Ax)` for `A ∈ GL(n, 𝔽₂)`. -/
def CubicPoly.comp {n : ℕ} (f : CubicPoly n) (A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    CubicPoly n :=
  CubicPoly.ofFun (fun x => f.eval (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) x))

end PlantedIQP


