-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_PerronProjection
-- name    : TarskiBootstrap_Dimensional_PerronProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:53.776795+00:00
-- url     : https://prove2.me/theorems/e52625e7-5da1-41a8-9d90-b91656362667
-- title:
--   Rank-one Perron projection
-- statement:
--   Given a real vector $v$ indexed by the original family, define
--
--   $$J[f,g]=v_fv_g,$$
--
--   that is, $J=vv^\top$. Nonnegativity, unit length and the Perron eigenvector equation are hypotheses of the matrix lemmas, not fields or conclusions of this definition.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, §3.2, following equation (3.6), PDF/printed p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Mathlib

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- J = vvᵀ, Section 3.2, p. 13. -/
def perronProjection {S : Type*} (v : S → ℝ) : Matrix S S ℝ :=
  fun f g => v f * v g

end TarskiBootstrap.Dimensional


