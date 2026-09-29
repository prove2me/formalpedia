-- Prove2me | Definitions.Def_EthierKurtz_diffusionBoundaryTests
-- name    : EthierKurtz_diffusionBoundaryTests
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:07:19.912975+00:00
-- url     : https://prove2.me/theorems/fe733756-b138-4bf4-a4ce-f7cd213d2407
-- title:
--   Scale and speed endpoint boundary tests
-- statement:
--   The pair of extended nonnegative endpoint integrals u and v formed from the scale and speed primitives, retaining divergence to infinity for Feller boundary classification.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equations (1.3)–(1.7), printed pp. 366–367 (PDF pp. 375–376).

import Definitions.Def_EthierKurtz_boundaryDriftPrimitive

open Filter MeasureTheory
open scoped Topology ENNReal

namespace EthierKurtz

/-- Endpoint values (u(e),v(e)) from (1.4)–(1.7). The signed primitives
m,p have the sign of x-r. Absolute values convert the oriented endpoint
integrals into nonnegative Lebesgue integrals, retaining +∞. -/
noncomputable def diffusionBoundaryTests (a b : ℝ → ℝ) (r : ℝ)
    (e : EReal) : ℝ≥0∞ × ℝ≥0∞ :=
  let B := boundaryDriftPrimitive a b r
  let m := fun x => ∫ y in r..x, 2 * Real.exp (B y) / a y
  let p := fun x => ∫ y in r..x, Real.exp (-B y)
  let J := {x : ℝ | min e (r : EReal) < (x : EReal) ∧
    (x : EReal) < max e (r : EReal)}
  (∫⁻ x in J, ENNReal.ofReal (|m x| * Real.exp (-B x)),
   ∫⁻ x in J, ENNReal.ofReal (|p x| * (2 * Real.exp (B x) / a x)))

end EthierKurtz


