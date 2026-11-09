-- Prove2me | Definitions.Def_ZamirInversion581_Mult_RankOneWalk
-- name    : ZamirInversion581_Mult_RankOneWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:34.509965+00:00
-- url     : https://prove2.me/theorems/f122f3a6-2664-4f7d-97fb-01cad676e025
-- title:
--   The rank-one walk operator $P$ on functions of matrices
-- statement:
--   For $f:F^{n\times n}\to\mathbb R$, the operator $P$ averages $f$ over a uniformly random rank-at-most-one perturbation:
--
--   $$
--   (Pf)(X)=\mathbb E_{u,v\sim F^n}\bigl[f(X+uv^\top)\bigr],
--   $$
--
--   with $u,v$ independent and uniform. Its iterate $P^r$ averages over $r$ independent such steps. Lemma 2.4 bounds the variance of $P^rf$.
--
--   **Formalization Note** $P$ is defined by this average, not through a spectrum.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.9, Lemma 2.4, definition of P; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- The rank-one walk operator of Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf
SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.9, Lemma 2.4:
`(P f)(X) = E_{u,v ∼ F^n}[f(X + u vᵀ)]`, with `u, v` independent and uniform. It is defined by this
average, not through a spectrum. -/
noncomputable def rankOneWalk {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) F → ℝ) : Matrix (Fin n) (Fin n) F → ℝ :=
  fun X => unifMean fun p : (Fin n → F) × (Fin n → F) => f (X + Matrix.vecMulVec p.1 p.2)

end ZamirInversion581.Mult


