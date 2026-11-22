-- Prove2me | Definitions.Def_NoHair_kerrNewmanTimeDirection
-- name    : NoHair_kerrNewmanTimeDirection
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T20:30:30.68181+00:00
-- url     : https://prove2.me/theorems/1974248f-a62f-48c4-a2b6-fb0cf69cad69
-- title:
--   The canonical future timelike direction in Kerr–Schild coordinates
-- statement:
--   Write $g=\eta+f k\otimes k$, with $k_0=1$. The vector field $T=\partial_t-\tfrac12 f\,\eta^{-1}k$ is the image of the Minkowski time unit under the Kerr–Schild shear. Its spatial components are $-fk_i/2$ and its time component is $1+f/2$.
-- source:
--   T. Adamo and E. T. Newman, The Kerr–Newman metric: A Review, section 3.1, https://arxiv.org/abs/1410.6626. Algebraic construction from the Kerr–Schild metric and null one-form.

import Definitions.Def_NoHair_kerrNewman

open scoped Manifold

namespace NoHair

/-- The Kerr–Schild shear applied to the future Minkowski time unit.
Its Cartesian components are (1 + f/2, -(f/2) k_spatial). -/
noncomputable def kerrNewmanTimeDirection (m a e : ℝ) : VecField (kerrNewmanSpacetime a) :=
  fun x =>
    let c := ksProfile m a e x.val / 2
    let k := ksNull a x.val
    (WithLp.toLp 2 ![1+c, -c*k 1, -c*k 2, -c*k 3] : E4)

end NoHair


