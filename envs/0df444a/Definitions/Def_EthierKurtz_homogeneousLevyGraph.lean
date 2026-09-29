-- Prove2me | Definitions.Def_EthierKurtz_homogeneousLevyGraph
-- name    : EthierKurtz_homogeneousLevyGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:26:59.464651+00:00
-- url     : https://prove2.me/theorems/bf6ea573-84e1-48bb-b4be-1aafe3a2a527
-- title:
--   Homogeneous Lévy generator graph
-- statement:
--   The full C-hat-two graph of the constant-coefficient compensated Lévy operator in the product uniform norm.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equation (3.22) and Theorem 3.4, printed p. 380 (PDF p. 389).

import Definitions.Def_EthierKurtz_diffusionOperator
import Definitions.Def_EthierKurtz_IsCTwiceVanishing

open MeasureTheory Filter
open scoped Topology ZeroAtInfty ContDiff

namespace EthierKurtz

/-- The full Ĉ² graph of (3.22) in the product uniform norm.
The compensation and local differential part are the exact constant specialization
of the existing levyTypeOperator; no finite-rate assumption is imposed. -/
def homogeneousLevyGraph {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d)) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    Set (C₀(EuclideanSpace ℝ (Fin d), ℝ) × C₀(EuclideanSpace ℝ (Fin d), ℝ)) :=
  {fg | IsCTwiceVanishing (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) ∧
    ∀ x, fg.2 x = diffusionOperator (fun _ => a) (fun _ => b) fg.1 x +
      ∫ y, (fg.1 (x + y) - fg.1 x -
        fderiv ℝ (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) x y / (1 + ‖y‖ ^ 2)) ∂μ}

end EthierKurtz


