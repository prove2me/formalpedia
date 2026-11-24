-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A0
-- name    : LL_S106SplitDecomp93_A0
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T16:00:13.587595+00:00
-- url     : https://prove2.me/theorems/650b2fc1-87ad-4956-b0da-b64a9d311d7b
-- title:
--   The prime sum $A_0=\sum_p \log p/(p\,(p-1))$
-- statement:
--   $A_0$ is the sum over all primes $p$ of $\log p/(p\,(p-1))$, written as a sum over all natural numbers with the non-prime terms equal to $0$; numerically $A_0=0.7553666108\ldots$.

import Mathlib

namespace LL_S106SplitDecomp93

noncomputable section

open Finset Real

def A0 : ℝ := ∑' p : ℕ, if p.Prime then Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) else 0

end

end LL_S106SplitDecomp93


