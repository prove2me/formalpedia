-- Prove2me | Definitions.Def_EthierKurtz_absorbedDiffusionGraph
-- name    : EthierKurtz_absorbedDiffusionGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:11:37.249974+00:00
-- url     : https://prove2.me/theorems/959682de-24e1-4464-9b97-62d489e856f4
-- title:
--   Absorbed diffusion generator graph
-- statement:
--   The graph of the elliptic operator on C²,μ functions over the region whose continuous operator trace vanishes on the boundary.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equations (1.15) and (1.17), printed p. 368 (PDF p. 377).

import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_closedRegionRestriction

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Exact absorbed graph. The second continuous coordinate supplies the
unique continuous extension of Gf, with zero values on the boundary.
On compact Ω̄, bounded continuous functions are exactly C(Ω̄). -/
def absorbedDiffusionGraph {d : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Set (((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)) :=
  {fg | let f := closedRegionRestriction fg.1
        let g := closedRegionRestriction fg.2
        CTwiceHolder Ω μ f ∧
        (∀ x ∈ Ω, g x = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
          a x i j * fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) + fderiv ℝ f x (b x)) ∧
        ∀ x ∈ frontier Ω, g x = 0}

end EthierKurtz


