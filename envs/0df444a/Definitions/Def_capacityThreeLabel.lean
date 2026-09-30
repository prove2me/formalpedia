-- Prove2me | Definitions.Def_capacityThreeLabel
-- name    : capacityThreeLabel
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T21:59:07.603389+00:00
-- url     : https://prove2.me/theorems/16cb0237-9e6c-4747-8825-be7df764adaa
-- title:
--   Canonical three-label block intensities and scores
-- statement:
--   For arbitrary real numbers $f_1,f_2,f_3$, define the canonical three-label and adjacent-pair intensities by
--
--   $$
--   \begin{aligned}
--   \gamma_{123}&=\min(f_1,\min(f_2,f_3)),\\
--   \gamma_{12}&=\max(\min(f_1,f_2)-f_3,0),\\
--   \gamma_{23}&=\max(\min(f_2,f_3)-f_1,0).
--   \end{aligned}
--   $$
--
--   For arbitrary real weights $q_{12},q_{23}$ and arbitrary real block values $x_{123},x_{12},x_{23}$, the weighted score is
--
--   $$
--   S_q(x)=x_{123}+q_{12}x_{12}+q_{23}x_{23}.
--   $$
--
--   The canonical score at $(f_1,f_2,f_3)$ is $S_q(\gamma)$, obtained by substituting the three displayed intensities. These five functions are defined for all real inputs: no positivity, normalization, probability law, or restriction on the weights is imposed by the definitions themselves. In particular, the triple intensity may be negative outside nonnegative-density applications.
--
--   The functions provide the pointwise block-score interface for three-label stability inequalities and their later measure-theoretic applications. They do not assert the existence of a coupling realizing any chosen block values.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), equations (2.4) and (3.2); CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Finite/ThreeLabel.lean, canonical123 (lines 17–18), canonical12 (20–21), canonical23 (23–24), threeScore (26–28), canonicalScore (30–33). Source-file SHA-256 6fdb4ddc257384df9f6df0a8f7c6083a32828efd6c2c0d06857e83cb1b204bb0. Source ranges are compiler-derived. Local source archive; no public repository URL, commit, or externally established authorship is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

set_option autoImplicit false

/-!
# The three-label scalar stability inequality

This file formalizes the finite, pointwise heart of the temporal capacity-flow
argument.  It contains no measure theory and no stochastic assumptions.

The variables `beta123`, `beta12`, `beta23`, and `beta13` are nonnegative
block intensities at one density point.  The three `cap` assumptions say that
the blocks using a label cannot exceed that label's available density.  The
`dij` variables are the pairwise maximality deficits.
-/

namespace FormalCapacity.Finite

/-- The intensity of the canonical three-label block. -/
def canonical123 (f1 f2 f3 : ℝ) : ℝ := min f1 (min f2 f3)

/-- The canonical `{1,2}`-block intensity. -/
def canonical12 (f1 f2 f3 : ℝ) : ℝ := max (min f1 f2 - f3) 0

/-- The canonical `{2,3}`-block intensity. -/
def canonical23 (f1 f2 f3 : ℝ) : ℝ := max (min f2 f3 - f1) 0

/-- The asymmetric block-additive score used by the capacity-flow witness. -/
def threeScore (q12 q23 x123 x12 x23 : ℝ) : ℝ :=
  x123 + q12 * x12 + q23 * x23

/-- The canonical score at densities `f1`, `f2`, `f3`. -/
def canonicalScore (q12 q23 f1 f2 f3 : ℝ) : ℝ :=
  threeScore q12 q23 (canonical123 f1 f2 f3)
    (canonical12 f1 f2 f3) (canonical23 f1 f2 f3)









end FormalCapacity.Finite


