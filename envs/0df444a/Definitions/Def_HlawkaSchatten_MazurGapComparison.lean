-- Prove2me | Definitions.Def_HlawkaSchatten_MazurGapComparison
-- name    : HlawkaSchatten_MazurGapComparison
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:42:10.04227+00:00
-- url     : https://prove2.me/theorems/f8102827-2a5e-446e-986d-53b2e2c7ef28
-- title:
--   Pair and triple gaps of a family after a possibly nonlinear map into a Hilbert space
-- statement:
--   Fix any type $E$ and a normed additive commutative group $H$. These three definitions require neither an addition operation on $E$ nor a scalar field or inner product on $H$. Let $N:E\to\mathbb{R}$ be any size functional and $\mathrm{map}:E\to H$ a possibly nonlinear map.
--
--   - `mappedPairGap N map x y` $:= N(x)+N(y)-\|\mathrm{map}(x)+\mathrm{map}(y)\|$
--   - `mappedTripleGap N map x y z` $:= N(x)+N(y)+N(z)-\|\mathrm{map}(x)+\mathrm{map}(y)+\mathrm{map}(z)\|$
--   - `mappedPairGapSum N map x y z` $:=$ the sum of the three `mappedPairGap` values on the triple $(x,y,z)$.
--
--   The point of naming these separately from `pairGap`/`tripleGap`/`pairGapSum` (`GapComparison` bundle) is the norm term: it is $\|\mathrm{map}(x)+\mathrm{map}(y)\|$, the norm of the *sum of images*, not $\|\mathrm{map}(x+y)\|$, the norm of the *image of the sum*. The later application takes $H$ to be a Hilbert space and uses its Hlawka inequality on the images. A possibly nonlinear map need not identify these two expressions.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/MazurGapComparison.lean#L23-L36

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Gap comparison through a nonlinear Mazur map

The Mazur map is not additive, so the Hilbert model for a family
`x, y, z` must use sums of the three *images*, rather than the image of
`x + y + z`.  This file records that distinction in the interface used by
the variational proof and carries out the final ordered-algebraic transfer.
-/

namespace HlawkaSchatten

variable {E H : Type*} [Add E]
  {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Two-body deficit of a family after applying a possibly nonlinear map
into a normed additive group. -/
def mappedPairGap (size : E → ℝ) (map : E → H) (x y : E) : ℝ :=
  size x + size y - ‖map x + map y‖

/-- Three-body deficit of a family after applying a possibly nonlinear map
into a normed additive group. -/
def mappedTripleGap (size : E → ℝ) (map : E → H) (x y z : E) : ℝ :=
  size x + size y + size z - ‖map x + map y + map z‖

/-- Sum of the three two-body mapped deficits. -/
def mappedPairGapSum (size : E → ℝ) (map : E → H) (x y z : E) : ℝ :=
  mappedPairGap size map x y + mappedPairGap size map x z +
    mappedPairGap size map y z

include 𝕜







end HlawkaSchatten


