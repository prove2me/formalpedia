-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_StoppingIndex
-- name    : TarskiBootstrap_Dimensional_StoppingIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:17.110528+00:00
-- url     : https://prove2.me/theorems/00f684ec-a8e1-47b7-8cc6-a0d3b6c68e15
-- title:
--   First nonfixed query block
-- statement:
--   For a tuple $\mathbf f=(f_1,\ldots,f_t)$ and query $\mathbf x=(x_1,\ldots,x_t)$, let
--
--   $$\sigma(\mathbf f,\mathbf x)=\min\{i:f_i(x_i)\ne x_i\},$$
--
--   with value $t+1$ when every block is fixed. The implementation uses zero-based indices, so its sentinel is $t$ and the other values are shifted down by one. It takes a minimum only of a nonempty finite set. This preserves the source stopping rule at every query.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Equation (3.2), PDF/printed p. 11, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Grid

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Equation (3.2), p. 11, shifted to zero-based indices; t denotes no failure. -/
noncomputable def firstNonfixed {n k t : ℕ+}
    (f : Fin (t : ℕ) → (Grid n k → Grid n k)) (x : Blocks n k t) : ℕ := by
  classical
  let failures := Finset.univ.filter (fun i => f i (x i) ≠ x i)
  exact if h : failures.Nonempty then (failures.min' h).val else (t : ℕ)

end TarskiBootstrap.Dimensional


