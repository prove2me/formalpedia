-- Prove2me | Definitions.Def_RandPurIso_Completion_opNorm
-- name    : RandPurIso_Completion_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:15.145701+00:00
-- url     : https://prove2.me/theorems/5e3560bd-b897-462b-82ad-19287095f158
-- title:
--   Operator norm $\|V\|_{op}$ (Definition 3.1)
-- statement:
--   For a linear map $V:A\to B$ between finite-dimensional Hilbert spaces,
--   $$\|V\|_{op}=\sup_{\||\varphi\rangle\|=1}\|V|\varphi\rangle\|.$$
--
--   **Formalization Note** The norm of $V$ as a continuous linear map between the Euclidean spaces $\mathbb C^X\to\mathbb C^Y$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.1, p. 17

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Operator norm** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.1, p. 17): `‖V‖_op = sup_{‖φ‖=1} ‖Vφ‖` for a linear
map `V : A → B`, i.e. the norm of `V` as a continuous linear map between the Euclidean spaces
`ℂ^X → ℂ^Y`. -/
noncomputable def opNorm {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (K : Matrix Y X ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)‖

end RandPurIso.Completion


