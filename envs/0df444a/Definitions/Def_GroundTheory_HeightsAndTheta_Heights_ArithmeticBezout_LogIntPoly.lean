-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:08.122737+00:00
-- url     : https://prove2.me/theorems/c697f431-72b4-4767-87fc-f36e94313fa8
-- title:
--   Log Int Poly
-- statement:
--   Definitions and structural lemmas for Log Int Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial
noncomputable section
namespace LogInt
variable {ι : Type*}
def indW (p : ι → Prop) [DecidablePred p] : ι → ℕ := fun x => if p x then 1 else 0
def scaleP (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) : ι → ℂ :=
  fun x => if p x then a * u x else u x
def polydisc (ι : Type*) (r : ℝ) : Set (ι → ℂ) := Set.univ.pi fun _ => Metric.closedBall 0 r
def nonHomog [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι ℂ) : Finset ι :=
  by classical exact Finset.univ.filter fun x => ¬ ∃ d, IsWeightedHomogeneous (indW (· = x)) g d
end LogInt
end
end GroundTheory.Heights₂.Heights


