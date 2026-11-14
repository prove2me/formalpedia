-- Prove2me | Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
-- name    : Kyprianou_Ch01_ExplicitLevyExamples
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:14:10.366831+00:00
-- url     : https://prove2.me/theorems/6169ea48-f003-4d3f-8a1a-ac4d226f1d1b
-- title:
--   Gamma Lévy measure and first-passage Laplace transforms for explicit Lévy examples
-- statement:
--   Reusable Chapter 1 example primitives: the gamma jump density β exp(−αx)/x on positive jumps, a continuous-path positive-level first-passage clock, and a Laplace factor that pays zero on infinite passage. Does not assert gamma, inverse Gaussian or stable theorems. All declarations still await remote elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 §§1.2.4–1.2.6, pp. 7–11.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

set_option autoImplicit false
namespace Kyprianou.Ch01
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The infinite-activity gamma Lévy measure on (0,∞). -/
noncomputable def gammaLevyMeasure
    (alpha beta : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun x => ENNReal.ofReal (beta * Real.exp (-alpha * x) / x))

/-- Strict upward first passage of a continuous drifted Brownian path. -/
noncomputable def firstUpperPassage
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  by
    classical
    exact if ∃ t : ℝ≥0, 0 < t ∧ s < X t ω then
      ((sInf ({t : ℝ≥0 | 0 < t ∧ s < X t ω} : Set ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)
    else ⊤

/-- A discounted passage-time transform, zero when passage never occurs. -/
noncomputable def passageLaplace
    (T : Ω → WithTop ℝ≥0) (q : ℝ) (ω : Ω) : ℝ :=
  match T ω with
  | none => 0
  | some t => Real.exp (-q * (t : ℝ))

end Kyprianou.Ch01


