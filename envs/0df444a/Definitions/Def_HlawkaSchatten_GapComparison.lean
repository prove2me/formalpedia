-- Prove2me | Definitions.Def_HlawkaSchatten_GapComparison
-- name    : HlawkaSchatten_GapComparison
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:41:54.939662+00:00
-- url     : https://prove2.me/theorems/f13a4a1f-d47f-411f-863d-f133a880174b
-- title:
--   Pair and triple gaps of a size functional, and the Hlawka-constant property
-- statement:
--   Fix a type $E$ with only an addition operation (Lean: `[Add E]`) — no norm, group, or other structure is assumed. Let $N:E\to\mathbb{R}$ be any real-valued "size" functional (Lean argument name `size`); it need not be a norm.
--
--   - `pairGap N x y` $:= N(x)+N(y)-N(x+y)$ — the pair deficit of $N$ at $x,y$: how far $N$ falls short of additivity on the pair.
--   - `tripleGap N x y z` $:= N(x)+N(y)+N(z)-N(x+y+z)$ — the triple deficit at $x,y,z$.
--   - `pairGapSum N x y z` $:=$ `pairGap N x y + pairGap N x z + pairGap N y z` — the sum of the three pair deficits of the triple.
--   - `HasHlawkaConstant N C` (a `Prop`) $:=$ for all $x,y,z\in E$, $\;\mathrm{tripleGap}\,N\,x\,y\,z \;\le\; C\cdot \mathrm{pairGapSum}\,N\,x\,y\,z$. This says $N$ satisfies a Hlawka-type inequality with constant $C$.
--
--   The source module goes on to prove (not part of this bundle) three short ordered-algebraic lemmas that transfer a Hlawka constant from one functional to another: if for some $m>0$ and $M\ge0$ the triple deficit of $N$ is at most $2M$ times the triple deficit of a "model" functional, each pair deficit of $N$ is at least $2m$ times the corresponding pair deficit of the model, and the model itself has Hlawka constant $1$, then $N$ has Hlawka constant $M/m$ (`tripleGap_le_ratio_mul_pairGapSum`, `hasHlawkaConstant_of_gapComparison`); and a strictly positive triple deficit together with a vanishing pair-deficit sum rules out every constant whatsoever (`no_hlawkaConstant_of_pairGapSum_eq_zero`).
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/GapComparison.lean#L20-L36

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Transferring Hlawka inequalities through gap comparisons

This file isolates the last, purely ordered-algebraic step in the
Bregman--Mazur proof of the dimension-independent Schatten Hlawka bound.
If the three-body gap for one size functional is bounded above by the gap
for a model functional, while every two-body gap is bounded below by the
corresponding model gap, then a Hlawka inequality for the model transfers.
-/

namespace HlawkaSchatten

variable {E : Type*} [Add E]

/-- The triangle-inequality deficit of a size functional at two vectors. -/
def pairGap (size : E → ℝ) (x y : E) : ℝ :=
  size x + size y - size (x + y)

/-- The triangle-inequality deficit of a size functional at three vectors. -/
def tripleGap (size : E → ℝ) (x y z : E) : ℝ :=
  size x + size y + size z - size (x + y + z)

/-- The sum of all three pair deficits associated to a triple. -/
def pairGapSum (size : E → ℝ) (x y z : E) : ℝ :=
  pairGap size x y + pairGap size x z + pairGap size y z

/-- A size functional satisfies the three-vector Hlawka inequality with constant `C`. -/
def HasHlawkaConstant (size : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap size x y z ≤ C * pairGapSum size x y z







end HlawkaSchatten


