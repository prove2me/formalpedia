-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A2
-- name    : LL_S106SplitDecomp93_A2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T16:27:46.865435+00:00
-- url     : https://prove2.me/theorems/27833f3e-026a-4477-b977-76397c320673
-- title:
--   The prime sum $A_2$ with weights $(8p^2-10p+4)\log^2p/(p^2(p-1)^2)$
-- statement:
--   $A_2$ is the sum over all primes $p$, including $p=2$, of $(8p^2-10p+4)\log^2 p/(p^2\,(p-1)^2)$; numerically $A_2=7.7015141851\ldots$.

import Mathlib

namespace LL_S106SplitDecomp93

noncomputable section

open Finset Real

def A2 : ℝ := ∑' p : ℕ, if p.Prime then
  (8 * (p : ℝ) ^ 2 - 10 * p + 4) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) *
    Real.log p ^ 2 else 0

end

end LL_S106SplitDecomp93


