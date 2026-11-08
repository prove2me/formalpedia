-- Prove2me | Definitions.Def_GaussianSweep_L0
-- name    : GaussianSweep_L0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:01.691212+00:00
-- url     : https://prove2.me/theorems/47cedfc2-9687-445c-b7dd-1c17a3610459
-- title:
--   $L_0 = |U| + |D \cap W|$
-- statement:
--   For a labeling $y$ of a graph $G$, with $U = \partial^- S_0$, $W = \partial^+ S_0$ and $D$ the set of switched vertices,
--   $$
--   L_0 = |U| + |D \cap W| .
--   $$
--   Together with $L_0'$ it controls the width of the connector bags of the median-switched layout at threshold zero.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.2), p.46 (PDF p.48)

import Mathlib
import Definitions.Def_GaussianSweep_innerFrontier
import Definitions.Def_GaussianSweep_outerFrontier
import Definitions.Def_GaussianSweep_switchD

namespace GaussianSweep

/-- `L₀ = |U| + |D ∩ W|` of Eq. (8.2) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.2), p.46 (PDF p.48)), where `U = ∂⁻S₀` and
`W = ∂⁺S₀`. -/
noncomputable def L0 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : V → ℝ) : ℕ :=
  (innerFrontier G y 0).card + (switchD G y ∩ outerFrontier G y 0).card

end GaussianSweep


