-- Prove2me | Definitions.Def_LL_Lemma3MV617Split_Itilde
-- name    : LL_Lemma3MV617Split_Itilde
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-25T13:05:57.499699+00:00
-- url     : https://prove2.me/theorems/8e3a62c5-0dc3-4a7a-a4fa-08cc7e5b6953
-- title:
--   The finite sum $\tilde I(m)=\sum_{P<k<m-P}(k(m-k))^{\beta-1}$
-- statement:
--   For real $\beta$, $P$ and an integer $m$, $\tilde I(m)$ is the real number $\sum (k(m-k))^{\beta-1}$ over integers $k$ with $0<k<m$, $P<k$ and $k<m-P$, where the power is the real power $x^{y}$ of Mathlib, defined for $x>0$ as $\exp(y\log x)$.

import Mathlib

namespace LL_Lemma3MV617Split

noncomputable section

open Real Finset ArithmeticFunction

noncomputable def Itilde (β P : ℝ) (m : ℤ) : ℝ :=
  ∑ k ∈ (Finset.Ioo (0 : ℤ) m).filter (fun k : ℤ => P < (k : ℝ) ∧ (k : ℝ) < (m : ℝ) - P),
    ((k : ℝ) * ((m : ℝ) - (k : ℝ))) ^ (β - 1)

end

end LL_Lemma3MV617Split


