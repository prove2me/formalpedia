-- Prove2me | Definitions.Def_GaussianSweep_L0prime
-- name    : GaussianSweep_L0prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:59.060752+00:00
-- url     : https://prove2.me/theorems/2bcc15b2-fbfd-4dd5-92a8-bffd98d433cd
-- title:
--   $L_0' = |W| + |D \cap U|$
-- statement:
--   For a labeling $y$ of a graph $G$, with $U = \partial^- S_0$, $W = \partial^+ S_0$ and $D$ the set of switched vertices,
--   $$
--   L_0' = |W| + |D \cap U| .
--   $$
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.2), p.46 (PDF p.48)

import Mathlib
import Definitions.Def_GaussianSweep_innerFrontier
import Definitions.Def_GaussianSweep_outerFrontier
import Definitions.Def_GaussianSweep_switchD

namespace GaussianSweep

/-- `L′₀ = |W| + |D ∩ U|` of Eq. (8.2) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.2), p.46 (PDF p.48)), where `U = ∂⁻S₀` and
`W = ∂⁺S₀`. -/
noncomputable def L0prime {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : V → ℝ) : ℕ :=
  (outerFrontier G y 0).card + (switchD G y ∩ innerFrontier G y 0).card

end GaussianSweep


