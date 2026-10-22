-- Prove2me | Definitions.Def_LiftedHuber
-- name    : LiftedHuber
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:17:47.454552+00:00
-- url     : https://prove2.me/theorems/e76c9f5b-0e5e-4c8a-9385-eb2852393077
-- title:
--   Lifted Huber extremal function of Theorem B
-- statement:
--   This module defines the common extremal function of Theorem B together with its analytic machinery. With the clipping map `clip t lo hi = max lo (min hi t)` and the Huber function $H_c(t) = t^2/2$ for $|t| \le c$, $H_c(t) = c|t| - c^2/2$ for $|t| \ge c$, the lifted Huber function associated with a unit vector $u$ is
--
--   $$f_N(z) = H_c\big(\langle u, z\rangle - 1\big) + \tfrac12\,\|z - \langle u, z\rangle\, u\|^2,$$
--
--   with the source's cutoff $c = 1/(2d_N+1)$. The orthogonal decomposition $z = tu + w$ with $w \perp u$ is realised by `orthProj u z = z - \langle u,z\rangle u` and its continuous-linear-map form `orthProjL`. The constant $B_N = c - c^2/2$ (`BN`) is the value of $f_N$ on the orthogonal complement $u^\perp$. The module establishes that $f_N$ is convex, differentiable and globally $1$-smooth with unique minimiser $u$ and $f_N(u) = 0$, and records the linear-branch formulas on $t \le 1 - c$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §25-26, eq. (25.1)-(25.3) and (26.1)-(26.6); Lean: FullFormalization.LiftedHuber lines 1-220

-- Generated from F:/20261008/FullFormalization\FullFormalization\LiftedHuber.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.LiftedHuber

  Source sections 25-26: the *common extremal function* of Theorem B.

  Fix `d j = j (j+7) / 8` (4.1) and a unit vector `u`.  With

      c = 1 / (2 d_N + 1)                                           (25.1)
      H_c(t) = t^2/2  for |t| ≤ c,   c |t| - c^2/2  for |t| ≥ c     (25.2)

  the source defines

      f_N(z) = H_c(⟪u,z⟫ - 1) + (1/2) ‖z - ⟪u,z⟫ u‖²                (25.3)

  Section 26 then records:

  * (26.1) the orthogonal decomposition `z = t u + w`, `w ⊥ u`, along which
    `f_N(z) = H_c(t - 1) + (1/2)‖w‖²`;
  * (26.2) the unique minimiser `z* = u`, `f_N* = 0`, `‖z*‖ = 1`;
  * (26.3) the gradient `∇f_N(z) = clip(⟪u,z⟫-1, -c, c) u + (z - ⟪u,z⟫ u)`,
    whose two summands live in the orthogonal subspaces `span u` and `u^⊥` and
    are each 1-Lipschitz, whence `f_N` is convex, differentiable and globally
    1-smooth;
  * (26.4)-(26.6) the linear-branch formulas on `t ≤ 1 - c`.

  Everything below is proved, nothing is postulated.  The single genuinely
  analytic point is `hasDerivAt_Hc`: the Huber function is differentiable
  everywhere, including at the two kinks `t = ±c`, where the quadratic and
  linear branches paste together smoothly.  Those two points are handled by
  gluing the one-sided derivatives with `HasDerivWithinAt.union`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The clipping map of (26.3) -/

/-- `clip t lo hi = max lo (min hi t)`, the source's `clip(·, -c, c)`. -/
noncomputable def clip (t lo hi : ℝ) : ℝ := max lo (min hi t)















/-! ### The Huber function (25.2) -/

/-- Source (25.2): `H_c(t) = t²/2` for `|t| ≤ c`, and `c|t| - c²/2` for
`|t| ≥ c`.  The two formulas agree when `|t| = c`, so this is the source's
function with its two-branch definition. -/
noncomputable def Hc (c t : ℝ) : ℝ :=
  if |t| ≤ c then t ^ 2 / 2 else c * |t| - c ^ 2 / 2











/-! ### Differentiability of the Huber function

The only non-elementary point is `|t| = c`, where the branch is a smooth paste
of `t²/2` and `c|t| - c²/2`: on `Iic c` the function agrees with `t²/2` near
`c`, on `Ici c` it agrees with `c t - c²/2`, and both one-sided derivatives at
`c` equal `c`.  The two one-sided statements are glued with
`HasDerivWithinAt.union`. -/







/-! ### Orthogonal decomposition in the direction `u` -/



/-- (26.1) the orthogonal part `w = z - ⟪u,z⟫ u` of `z`. -/
noncomputable def orthProj (u z : E) : E := z - ⟪u, z⟫ • u

/-- The same projection, as a continuous linear map. -/
noncomputable def orthProjL (u : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ContinuousLinearMap.smulRight (innerSL ℝ u) u











/-! ### The gradient of `H_c(⟪u,·⟫ - 1)` -/



/-! ### The gradient of `(1/2)‖z - ⟪u,z⟫ u‖²` -/



/-! ### The lifted Huber function (25.3) -/

/-- Source (25.3) with a general cutoff `c` and a unit vector `u`:
`f(z) = H_c(⟪u,z⟫ - 1) + (1/2)‖z - ⟪u,z⟫ u‖²`. -/
noncomputable def liftedHuberWith (c : ℝ) (u : E) : E → ℝ :=
  fun z => Hc c (⟪u, z⟫ - 1) + (1 / 2) * ‖z - ⟪u, z⟫ • u‖ ^ 2

/-- Source (25.3) with the source's own cutoff `c = 1/(2 d_N + 1)` (25.1). -/
noncomputable def liftedHuber (u : E) (N : ℕ) : E → ℝ :=
  liftedHuberWith (1 / (2 * d N + 1)) u







/-! ### The gradient (26.3) -/







/-! ### Convexity, via monotonicity of the gradient -/







/-! ### The gradient is globally 1-Lipschitz

The first summand of (26.3) lies in `span u`, the second in `u^⊥`; the two
components of `a - b` decompose the same way, so Pythagoras reduces the claim to
the 1-Lipschitzness of the clipping. -/



/-! ### The minimum of the lifted Huber function (26.2) -/







/-! ### The linear branch (26.4)-(26.6) -/





/-! ### The source's cutoff, and the specialization to `liftedHuber` -/

/-- Source (26.6): `B_N = c - c²/2`. -/
noncomputable def BN (_N : ℕ) (c : ℝ) : ℝ := c - c ^ 2 / 2



























end FullFormalization


