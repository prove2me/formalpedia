-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_TensorTerm
-- name    : TarskiBootstrap_Dimensional_TensorTerm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:40.546393+00:00
-- url     : https://prove2.me/theorems/2cdd4de8-8931-4a1f-a1a3-94fa23bb5fb9
-- title:
--   Ordered tensor factors for one chain position
-- statement:
--   For a positive integer $t$, a real matrix $\Gamma_0$ and vector $v$, with $J=vv^\top$, define
--
--   $$\Gamma_i=I^{\otimes(i-1)}\otimes\Gamma_0\otimes J^{\otimes(t-i)}.$$
--
--   The entry between tuples $\mathbf f,\mathbf g$ is the product of the corresponding factor entries. Identity factors precede $i$, the $\Gamma_0$ factor is at $i$, and $J$ factors follow it. The code uses zero-based block positions without truncated tensor powers. No spectral estimate is part of this definition.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Equations (3.5)–(3.6), PDF/printed p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Grid
import Definitions.Def_TarskiBootstrap_Dimensional_PerronProjection

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Equations (3.5)–(3.6), p. 13: identity before i, Γ₀ at i, J after i. -/
noncomputable def tensorTerm {S : Type*} (t : ℕ+) (Γ₀ : Matrix S S ℝ)
    (v : S → ℝ) (i : Fin (t : ℕ)) : Matrix (Fin (t : ℕ) → S) (Fin (t : ℕ) → S) ℝ := by
  classical
  exact fun f g => ∏ j : Fin (t : ℕ),
    if j < i then (if f j = g j then 1 else 0)
    else if j = i then Γ₀ (f j) (g j)
    else perronProjection v (f j) (g j)

end TarskiBootstrap.Dimensional


