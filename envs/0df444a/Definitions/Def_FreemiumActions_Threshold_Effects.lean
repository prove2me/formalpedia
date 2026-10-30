-- Prove2me | Definitions.Def_FreemiumActions_Threshold_Effects
-- name    : FreemiumActions_Threshold_Effects
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:59:30.849385+00:00
-- url     : https://prove2.me/theorems/4518e2da-1914-49af-8667-7e333835ca16
-- title:
--   Paired policies and their visit and revenue effects
-- statement:
--   Fix one stationary baseline policy $y$. For each switch state $b$, $y_b^1$ equals $y$ except that it removes the offer at $b$, and $y_b^2$ equals $y$ except that it offers at $b$. Define
--   $$\Delta n(e\mid b)=n_{y_b^2}(b,e)-n_{y_b^1}(b,e),\quad \Delta r(e\mid b)=r(e,y_b^2(e))-r(e,y_b^1(e)),$$
--   $$C(b)=n_{y_b^2}(b,b)r(b,1)-n_{y_b^1}(b,b)r(b,0),\qquad F(b)=\sum_{e>b}\Delta n(e\mid b)r(e,y(e)).$$
--   The baseline stays fixed as $b$ varies. Counts are defined from infinite transition powers, not by the inverse product formula. Signed differences and benefits take values in the extended reals, which agree with ordinary real subtraction on these finite quantities under the model assumptions. In particular $C(N)$ uses its original visit definition rather than an interior-only formula.
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §4, pp. 12–14 (PDF pp. 12–14), equations (10), (14), (15); catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Values

namespace FreemiumActions.Threshold

def localPolicy {N : ℕ} (y : Policy N) (b : Level N) (u : Bool) : Policy N :=
  Function.update y b u

noncomputable def deltaVisits {N : ℕ} (d : Data N) (y : Policy N)
    (e b : Level N) : EReal :=
  (visits d (localPolicy y b true) b e).toEReal -
    (visits d (localPolicy y b false) b e).toEReal

noncomputable def deltaReward {N : ℕ} (d : Data N) (y : Policy N)
    (e b : Level N) : ℝ :=
  reward d e (localPolicy y b true e) - reward d e (localPolicy y b false e)

noncomputable def currentBenefit {N : ℕ} (d : Data N) (y : Policy N)
    (b : Level N) : EReal :=
  (visits d (localPolicy y b true) b b * ENNReal.ofReal (reward d b true)).toEReal -
    (visits d (localPolicy y b false) b b * ENNReal.ofReal (reward d b false)).toEReal

noncomputable def futureBenefit {N : ℕ} (d : Data N) (y : Policy N)
    (b : Level N) : EReal :=
  ∑ e ∈ Finset.univ.filter (fun e => b < e),
    deltaVisits d y e b * (reward d e (y e) : EReal)

end FreemiumActions.Threshold


