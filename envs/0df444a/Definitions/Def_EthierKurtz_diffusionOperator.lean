-- Prove2me | Definitions.Def_EthierKurtz_diffusionOperator
-- name    : EthierKurtz_diffusionOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:01:47.268232+00:00
-- url     : https://prove2.me/theorems/1b28d31f-fa1f-46de-ba0e-730cccceb3aa
-- title:
--   Diffusion operator
-- statement:
--   The second-order diffusion operator with one-half of the covariance-weighted Hessian trace plus the drift directional derivative.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equation (1.15), printed p. 368 (PDF p. 377).

import Mathlib

open Filter
open scoped Topology ZeroAtInfty ContDiff

namespace EthierKurtz

/-- Equation (1.15). Matrices act on Euclidean space as continuous linear maps;
their entries are recovered in the standard orthonormal basis. -/
noncomputable def diffusionOperator {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
    (a x (EuclideanSpace.single j 1)) i *
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) + fderiv ℝ f x (b x)

end EthierKurtz


