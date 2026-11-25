-- Prove2me | Definitions.Def_LL_Lemma3MV617Split_Ttilde
-- name    : LL_Lemma3MV617Split_Ttilde
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-25T13:09:22.257565+00:00
-- url     : https://prove2.me/theorems/5d67f771-92fa-413d-850b-bfea1d6262e4
-- title:
--   The exceptional exponential sum $\tilde T(\eta)=-\sum_{P<n\le X}n^{\beta-1}e(n\eta)$
-- statement:
--   For real $\beta,P,X,\eta$, $\tilde T(\eta)=-\sum_{n}n^{\beta-1}e(\eta n)\in\mathbb C$, the sum running over natural numbers $n$ with $\lfloor P\rfloor_+<n\le\lfloor X\rfloor_+$, where $\lfloor\cdot\rfloor_+$ is the natural number floor, equal to $0$ on negative reals.

import Mathlib
import Definitions.Def_LL_Lemma3MV617Split_eC

namespace LL_Lemma3MV617Split

noncomputable section

open Real Finset Filter

noncomputable def Ttilde (β P X η : ℝ) : ℂ :=
  -∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, (((n : ℝ) ^ (β - 1) : ℝ) : ℂ) * eC (η * n)

end

end LL_Lemma3MV617Split


