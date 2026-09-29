-- Prove2me | Definitions.Def_EthierKurtz_CTwiceHolder
-- name    : EthierKurtz_CTwiceHolder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:09:30.321159+00:00
-- url     : https://prove2.me/theorems/8dcf7490-49e0-40dd-a1a1-ffdf2adac07e
-- title:
--   Interior C²,μ regularity
-- statement:
--   A twice continuously differentiable scalar function whose ordered second partial derivatives satisfy the componentwise local Hölder condition.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equation (1.14), printed p. 368 (PDF p. 377).

import Definitions.Def_EthierKurtz_ComponentHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- C^{2,μ} on an open set; ordered second partials cover the multiindices
of order two in (1.14). Values outside the open set are immaterial. -/
def CTwiceHolder {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (μ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiffOn ℝ 2 f Ω ∧ ∀ i j : Fin d,
    ComponentHolder Ω μ (fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1))

end EthierKurtz


