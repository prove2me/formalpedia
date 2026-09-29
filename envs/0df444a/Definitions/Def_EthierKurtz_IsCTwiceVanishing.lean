-- Prove2me | Definitions.Def_EthierKurtz_IsCTwiceVanishing
-- name    : EthierKurtz_IsCTwiceVanishing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:26:23.60863+00:00
-- url     : https://prove2.me/theorems/cc8fac87-90f5-467b-aa0b-0a1ede398be5
-- title:
--   Twice differentiable functions vanishing through second order
-- statement:
--   The C² functions whose values and every first and second coordinate derivative vanish at infinity.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 2, equation (2.6), printed p. 373 (PDF p. 382).

import Mathlib

open MeasureTheory Filter
open scoped Topology ZeroAtInfty ContDiff

namespace EthierKurtz

/-- The source's Ĉ²: the function and every partial derivative through order
two vanish at infinity. Equation (2.6), p. 373, with γ = 0. -/
def IsCTwiceVanishing {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧
  Tendsto f (cocompact _) (𝓝 0) ∧
  (∀ i : Fin d, Tendsto (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
    (cocompact _) (𝓝 0)) ∧
  ∀ i j : Fin d, Tendsto (fun x =>
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1)) (cocompact _) (𝓝 0)

end EthierKurtz


