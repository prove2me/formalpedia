-- Prove2me | Definitions.Def_LineVsPoint_dirDeriv
-- name    : LineVsPoint_dirDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:05.433328+00:00
-- url     : https://prove2.me/theorems/082e17de-516e-41c4-bfa1-c5869731114d
-- title:
--   Directional derivative $D_\lambda=\lambda_X\partial_X+\lambda_Y\partial_Y+\lambda_Z\partial_Z$
-- statement:
--   For $\lambda=(\lambda_X,\lambda_Y,\lambda_Z)\in\mathbb F^3$ and $B\in\mathbb F[X,Y,Z]$, the **directional derivative** is
--
--   $$
--   D_\lambda B:=\lambda_X\,\partial_X B+\lambda_Y\,\partial_Y B+\lambda_Z\,\partial_Z B,
--   $$
--
--   with formal partial derivatives. In Section 3 the paper uses $S=D_\lambda A$ for the interpolant $A$ and a direction $\lambda$ with $\gcd(A,S)=1$.
--
--   **Formalization Note** The partial derivatives are `MvPolynomial.pderiv`.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.3, p.11; §3.2, p.15

import Mathlib

set_option autoImplicit false

namespace LineVsPoint

/-- The **directional derivative** `D_λ := λ_X ∂_X + λ_Y ∂_Y + λ_Z ∂_Z` applied to
`B ∈ F[X, Y, Z]`, with formal partial derivatives: Dao, Kominers, Thaler, Zheng, *Cube-Root
Soundness Is Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 2.3,
p.11, and `S = λ_X A_X + λ_Y A_Y + λ_Z A_Z` of §3.2, p.15.

**Formalization Note.** `X, Y, Z` are the variables `0, 1, 2` of `MvPolynomial (Fin 3) F`,
`λ = (lam 0, lam 1, lam 2)`, and `∂` is `MvPolynomial.pderiv` (formal, as §2.1 requires). -/
noncomputable def dirDeriv {F : Type*} [Field F] (lam : Fin 3 → F)
    (B : MvPolynomial (Fin 3) F) : MvPolynomial (Fin 3) F :=
  ∑ i, lam i • MvPolynomial.pderiv i B

end LineVsPoint


