-- Prove2me | Definitions.Def_GevreyGibbsSep_Hnu
-- name    : GevreyGibbsSep_Hnu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:38.062319+00:00
-- url     : https://prove2.me/theorems/1bce3105-548f-4b1d-8d3c-c6b20df1764c
-- title:
--   Translated step $H_\nu$
-- statement:
--   The step of width $\nu>0$ is $\theta_\nu(x)=\theta_1(x/\nu)$, and its translate is
--   $$H_\nu(x)=\theta_\nu(x-\nu)=\theta_1(x/\nu-1),$$
--   which vanishes for $x\le0$ and equals $1$ for $x\ge2\nu$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.5, pp.37–38

import Mathlib
import Definitions.Def_GevreyGibbsSep_theta1

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The translated step `H_ν(x) = θ_ν(x − ν) = θ₁(x/ν − 1)` (arXiv:2608.24527 (sha256
d4fd40eb…), Definition B.5, pp.37–38). -/
noncomputable def Hnu (s ν x : ℝ) : ℝ := theta1 s (x / ν - 1)

end GevreyGibbsSep


