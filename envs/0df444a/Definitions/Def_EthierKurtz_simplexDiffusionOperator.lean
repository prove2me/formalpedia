-- Prove2me | Definitions.Def_EthierKurtz_simplexDiffusionOperator
-- name    : EthierKurtz_simplexDiffusionOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:16:08.585321+00:00
-- url     : https://prove2.me/theorems/2d22997b-851a-46e9-ad57-a6d4d545cf4d
-- title:
--   Degenerate diffusion operator on the simplex
-- statement:
--   The second-order operator whose covariance matrix has entries x_i(δ_ij−x_j), with one half multiplying the covariance-weighted second derivatives, plus the directional first-derivative term from the drift b.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 2, equation (2.15), printed p. 375 (PDF p. 384), and Chapter 8, Section 1, equation (1.15), printed p. 368 (PDF p. 377).

import Definitions.Def_EthierKurtz_WFState

open Filter
open scoped Topology BigOperators ContDiff NNReal
namespace EthierKurtz

/-- Equations (1.15), (2.15): simplex covariance and arbitrary inward drift.
Only the covariance sum is multiplied by 1/2. -/
noncomputable def simplexDiffusionOperator {d : ℕ}
    (b : WFState d → Fin d → ℝ) (f : (Fin d → ℝ) → ℝ)
    (x : WFState d) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, x.val i * ((if i = j then 1 else 0) - x.val j) *
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x.val (Pi.single i 1)) +
    ∑ i, b x i * fderiv ℝ f x.val (Pi.single i 1)

end EthierKurtz


