-- Prove2me | Definitions.Def_Scaling
-- name    : Scaling
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:27:01.064981+00:00
-- url     : https://prove2.me/theorems/27ab2edb-eeed-4497-a755-2e3d50890a48
-- title:
--   Radius/smoothness rescaling $f(x) = LR^2 f_N((x-x_{\mathrm{init}})/R)$ and the normalised loss $q_{A,N}$
-- statement:
--   This module formalises the change of scale used in §19 and §32, which manufactures a general instance from a *normalised* function $f_N$ (optimiser $u$, initial point $0$, $L = R = 1$):
--
--   $$f(x) = L R^2\, f_N\!\left(\frac{x - x_{\mathrm{init}}}{R}\right), \qquad \frac{x - x_{\mathrm{init}}}{R} = \tfrac{1}{R} \bullet (x - x_{\mathrm{init}}),$$
--
--   where $x_{\mathrm{init}}$ is the public initial point, $R > 0$ the public radius and $L$ the declared smoothness constant. The normalised coordinate is written with the reciprocal *scalar* $1/R \bullet (x - x_{\mathrm{init}})$, since there is no division of a vector by a scalar, and it is exposed as `scaledArg`, with `scaledAffine` its affine-map packaging used to transport convexity and differentiability. The module also introduces the normalised excess loss
--
--   $$\mathrm{normalizedLoss}(L, R, f, f^\star, x_{\mathrm{out}}) = \frac{f(x_{\mathrm{out}}) - f^\star}{L R^2},$$
--
--   i.e. the value $q_{A,N}$ before normalisation; its exact invariance under the rescaling, together with the identity of the normalised and general trajectories, is what the precise content of *every $q_{A,N}$ stays unchanged* amounts to.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §19 (source lines 1778-1816) and §32, eq. (32.1) (lines 2688-2751); Lean: FullFormalization.Scaling lines 1-178

-- Generated from F:/20261008/FullFormalization\FullFormalization\Scaling.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.Scaling

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 19 and 32.

  Section 19 ("恢复一般 `L,R`", source lines 1638-1650 of the `### 19.` block) and
  section 32 (source lines 2688-2751) are the same argument in two places: starting
  from a *normalised* function `f_N` (optimiser `u`, initial point `0`, `L = R = 1`)
  one manufactures a general instance by

      f(x) = L R^2 f_N((x - x_init)/R)                                   (32.1)

  and the source records four consequences:

    (i)   ∇f(x) = L R ∇f_N((x - x_init)/R);
    (ii)  ‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖                                 (L-smoothness);
    (iii) the optimiser is x⋆ = x_init + R u, at distance R from x_init;
    (iv)  "由于算法均按公开 R 在 normalized coordinates 中运行，归一化轨迹与
          L = R = 1 完全一致，所以所有 q_{A,N} 保持不变" — i.e. the *normalised*
          trajectory (and therefore every normalised loss `q_{A,N}`) is unchanged.

  Representation choices (recorded here because they are genuine formalisation
  decisions, not transcription):

  * `(x - x_init)/R` is written `(1/R) • (x - x_init)`.  Mathlib has no division
    `· / ·` of a vector by a scalar; `1/R` is the reciprocal *scalar* and the two
    expressions are identical field-theoretically.  No other mathematical content
    is hidden in this rewriting.

  * The source's claim (iii) `‖x⋆ - x_init‖ = R` is *not* a consequence of
    admissibility alone: `Admissible 1 1 fN 0 u` only supplies `‖u‖ ≤ 1`
    (this is exactly its `within_radius` field, since the normalized initial point
    is `0`).  What is proved here is the general identity
    `‖(x_init + R • u) - x_init‖ = R * ‖u‖` (`scaled_star_dist`) together with
    the specialisation `= R` under the extra hypothesis `‖u‖ = 1`
    (`scaled_star_dist_eq`).  For the extremisers used in the lower bounds of
    sections 20-31 one has `‖u‖ = 1`, so the source's sentence is recovered
    there; for a general admissible function it would be false (take `f_N = ‖·‖²`,
    `u = 0`).  This is recorded as a *precision* of the source, not a change of
    claim: the sentence is applied in the source only to the extremiser, whose
    `u` does satisfy `‖u‖ = 1`.

  * The transfer of `Admissible`/`AdmissibleUnique` (item (iii)) instantiates the
    admissible class with initial point `x_init` and optimiser `x_init + R • u`.
    Its `within_radius` field then reads `‖x_init - (x_init + R • u)‖ ≤ R`, which is
    exactly the normalised bound `‖u‖ ≤ 1` transported by the scaling — the
    radius hypothesis is *carried along* by the construction rather than added.

  * Item (iv) is formalised as an exact identity between the two trajectories
    (`nagX_scaled`, `nagY_scaled`) plus the exact invariance of the normalised
    loss (`normalizedLoss_scaled`, `normalizedLoss_scaled_nagX`).  This is the
    precise content of "every `q_{A,N}` is unchanged".
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_RationalNAG

open scoped Gradient

-- Several lemmas below are purely metric/affine and never use completeness of
-- `E` (which the section variable carries because `gradient` requires it).
set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1.  The scaling map (32.1) -/

/-- The normalised coordinate `(x - x_init)/R` of source (32.1), written with the
reciprocal scalar because Mathlib has no vector-by-scalar division:
`(x - x_init)/R = (1/R) • (x - x_init)` for `R ≠ 0`.

(`1/R` is the reciprocal in `ℝ`; when `R = 0` this is the junk value `0`, which is
why every statement below that uses it carries `R ≠ 0` or `0 < R`.) -/
noncomputable def scaledArg (R : ℝ) (x_init : E) : E → E :=
  fun x => (1 / R) • (x - x_init)

/-- Source (32.1): `f(x) = L R^2 f_N((x - x_init)/R)`.

`f_N` is the *normalised* function (optimiser `u`, initial point `0`, `L = R = 1`);
`x_init` and `R` are the public position and radius of the general instance, and
`L` is the declared smoothness constant. -/
noncomputable def scaled (L R : ℝ) (x_init : E) (fN : E → ℝ) : E → ℝ :=
  fun x => L * R ^ 2 * fN (scaledArg R x_init x)













/-- The normalising coordinate map, as an affine map.  Used only to transport
convexity (with `ConvexOn.comp_affineMap`) and differentiability. -/
noncomputable def scaledAffine (R : ℝ) (x_init : E) : E →ᵃ[ℝ] E :=
  AffineMap.mk' (scaledArg R x_init) ((1 / R) • (LinearMap.id : E →ₗ[ℝ] E)) x_init (by
    intro p
    simp [scaledArg, vsub_eq_sub, vadd_eq_add])



/-! ## 2.  Gradient scaling (source line 2716)

`∇f(x) = L R ∇f_N((x - x_init)/R)`. -/













/-! ## 3.  Smoothness transfer (source line 2722)

`∀x y, ‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖` whenever the normalised gradient is
1-Lipschitz. -/



/-! ## 4.  Differentiability and convexity transfer -/





/-! ## 5.  The optimiser is transported (source lines 2737-2747) -/











/-! ## 6.  Trajectory invariance (source line 2749)

"归一化轨迹与 `L = R = 1` 完全一致" — the scaled trajectory is the affine image of
the normalised one, `k ↦ x_init + R • (normalised iterate)`.  Consequently every
quantity computed on the normalised trajectory (in particular every `q_{A,N}`) is
unchanged. -/







/-! ## 7.  Invariance of the normalised loss `q_{A,N}` (source line 2749) -/

/-- The normalised excess loss of a general instance, i.e. `q_{A,N}` before the
normalisation step: `(f x_out - f⋆) / (L R^2)`. -/
noncomputable def normalizedLoss (L R : ℝ) (f : E → ℝ) (fstar : ℝ) (xout : E) : ℝ :=
  (f xout - fstar) / (L * R ^ 2)





end FullFormalization


