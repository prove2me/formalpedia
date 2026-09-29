-- Prove2me | Definitions.Def_EthierKurtz_obliqueDiffusionGraph
-- name    : EthierKurtz_obliqueDiffusionGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:13:51.214419+00:00
-- url     : https://prove2.me/theorems/784345af-87d1-4395-ba40-3c69218305fc
-- title:
--   Obliquely reflected diffusion generator graph
-- statement:
--   The reflected elliptic graph whose continuous derivative trace satisfies the oblique boundary condition and whose second coordinate continuously extends the interior operator.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equations (1.15), (1.19), and (1.20), printed pp. 368–369 (PDF pp. 377–378).

import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_closedRegionRestriction

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Exact graph (1.20). Boundary derivatives are continuous extensions
of interior derivatives; a zero extension is never differentiated there.
The second graph coordinate similarly extends Gf from the interior. -/
def obliqueDiffusionGraph {d : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Set (((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)) :=
  {fg | let f := closedRegionRestriction fg.1
        let g := closedRegionRestriction fg.2
        CTwiceHolder Ω μ f ∧
        (∀ x ∈ Ω, g x = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
          a x i j * fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) + fderiv ℝ f x (b x)) ∧
        ∃ J : (closure Ω) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
          Continuous J ∧
          (∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin d)) ∈ Ω →
            J x = fderiv ℝ f x) ∧
          ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin d)) ∈ frontier Ω →
            J x (c x) = 0}

end EthierKurtz


