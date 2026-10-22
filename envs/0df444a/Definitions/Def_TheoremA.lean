-- Prove2me | Definitions.Def_TheoremA
-- name    : TheoremA
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:27:51.604057+00:00
-- url     : https://prove2.me/theorems/3ab9c67c-7bb1-4336-a731-54a9c32ce57e
-- title:
--   Theorem A: sharp bound $\sup_f (f(x_N)-f^\star)/(LR^2) = \tau_N$ for rational-momentum NAG
-- statement:
--   This module assembles Theorem A of the manuscript: for a differentiable convex $f$ on a finite-dimensional Euclidean space whose gradient is globally $L$-Lipschitz and which has a minimiser $x^\star$ at distance at most $R$ from the initial point, the rational-momentum Nesterov output $x_N$ satisfies the exact sharp bound
--
--   $$\sup_f \frac{f(x_N) - f^\star}{L R^2} = \tau_N = \frac{2}{N^2 + 7N + 4}, \qquad N \ge 1,$$
--
--   where $x_N$ is the final extrapolated iterate of §3 and $\tau_N$ is the sharp constant. Its three constituents are the normalised upper bound (1.1)/(17.1) $F_N - f^\star \le \tau_N \|r\|^2$, its general $L, R$ form (19.1) obtained through the rescaling (32.1), and the matching one-dimensional Huber attainment of §20 (20.4) that pins the supremum from below. The single mathematical object introduced here is the affine change of coordinates $z \mapsto x^\star + R \bullet z$ (`affineShift`), the inverse of `Scaling.scaledArg`, used to transport convexity onto the normalised function. Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe` occurs.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §17-§20, eq. (1.1)/(17.1), (18.1), (19.1), (20.4) (Theorem A, source lines 17-56, boxed (A)); Lean: FullFormalization.TheoremA lines 1-113

-- Generated from F:/20261008/FullFormalization\FullFormalization\TheoremA.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.TheoremA

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`.
  Theorem A (source lines 17-56, boxed at line 3002) assembled from the pieces
  that are already verified elsewhere in this development.

  The three layers:

  * `nag_upper_bound_normalized` — (1.1)/(17.1) in the normalised setting
    `L = 1`, `x⋆ = 0`, `f⋆ = 0`, where the initial point is `r` and the radius is
    `‖r‖`: `F_N - f⋆ = F_N ≤ τ_N ‖r‖²`.  For `N ≥ 2` this is the master
    certificate (7.1) of section 12 — `CertificateIdentities` (9.1), (10.1),
    (11.1), (11.2) fed into `MasterCertificate.telescope` — combined with the
    nonnegativity of the interpolation residual (2.2), of the square terms
    (sections 14-16) and of the weights (section 13).  For `N = 1` it is the
    dedicated certificate (18.1) of section 18 (`NAGUpperBound.boundary_bound`),
    whose value `1/6` is exactly `τ_1`, so the two branches join without gap.

  * `theorem_A_upper` — the general `L, R` form (19.1)/(32.1).  Given an
    admissible `f` with optimiser `x⋆` and `‖x₀ - x⋆‖ ≤ R`, the normalised
    function is `f_N y = (f (x⋆ + R y) - f⋆)/(L R²)`, which is
    `NormalizedAtZero`; `Scaling.gradient_scaled` and `Scaling.differentiable_scaled`
    (with the local `gradient_normalized`/`gradient_const_add`) show that both
    NAG trajectories are related by `x_k = x⋆ + R · x_k^N` (proved directly, as
    in `Scaling.nag_pair_scaled`, but starting from the general `x₀`), and
    `nag_upper_bound_normalized` applied to `f_N` then gives the bound.

  * `theorem_A_attainment` / `theorem_A` / `theorem_A_sup` — the equality case of
    section 20: the one-dimensional Huber function (`Huber1D.huber_attainment`)
    is `NormalizedAtZero` and attains `τ_N` exactly.  **The supremum claim is
    stated in both forms**: `theorem_A_sup` is the literal `sSup` statement, and
    `theorem_A` is the equivalent pair "every admissible function satisfies the
    upper bound" ∧ "some admissible function attains it".  The pair form is the
    one used to *prove* the supremum (upper half + attained value), and the two
    forms are equivalent, so neither weakens the mathematics.
    (`theorem_A_attainment_admissible` records the same attainment in the
    source's own `Admissible`-class vocabulary.)

  **Scalar-multiplication pitfall** (hit three times earlier in this project):
  a bare `(1/2) • v` elaborates the numeral at type `ℕ`.  Every scalar in this
  file is written with an explicit `ℝ` ascription, e.g. `((1 : ℝ) / 2) • v`.

  Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_NAGUpperBound
import Definitions.Def_Positivity
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### (1.1) / (17.1): the upper bound in the normalised setting -/



/-! ### Auxiliary gradient lemmas for the scaling (32.1) -/







/-- The affine map `z ↦ x⋆ + R • z`; `Scaling.scaledAffine` is the reverse
coordinate change `x ↦ (x - x⋆)/R`.  It transports convexity to the
normalised function. -/
noncomputable def affineShift (R : ℝ) (xstar : E) : E →ᵃ[ℝ] E :=
  AffineMap.mk' (fun z : E => xstar + R • z) (R • (LinearMap.id : E →ₗ[ℝ] E)) 0 (by
    intro p
    simp only [vsub_eq_sub, vadd_eq_add, sub_zero, smul_zero, add_zero]
    abel)



/-! ### (19.1): the general `L, R` upper bound -/



/-! ### (20.4): the matching lower bound, and Theorem A -/











end FullFormalization


