-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_EffectiveGaps
-- name    : CorruptRobustRL_Supervised_Supplement_EffectiveGaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:09:09.628576+00:00
-- url     : https://prove2.me/theorems/e2c2909b-75e4-4ee2-8b83-34b251ce9e0e
-- title:
--   Effective stage gaps and the low threshold, (C.5)
-- statement:
--   Let $S=|\mathcal X|$, $A=|\mathcal A|$, $H$ be the horizon, $g_h(x,a)$ the stage gap and $g_{\min}$ the minimum positive stage gap. Define
--   $$\check g_h(x,a)=\max\left\{\frac{g_{\min}}{8H^2},\frac{g_h(x,a)}{8H}\right\},\qquad \check g_{\min,\mathrm{low}}=\frac{g_{\min}}{64SAH^3}.$$
--   These are the two thresholds used by (C.6) and (C.7). The checked error has an additional division of its threshold by four. All denominators are evaluated in the real numbers; the results use $H\ge1$ and a nominal initial distribution, which ensures a nonempty state space.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 44, (C.5)

import Definitions.Def_CorruptRobustRL_Supervised_Supplement_StageGaps

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X] [Fintype A] [Nonempty A]

/-- Effective stage gap of (C.5), before the additional division by 4 in (C.6). -/
noncomputable def checkedGap (M : NominalMDP X A) (H h : ℕ) (x : X) (a : A) : ℝ :=
  max (gapMin M H / (8 * (H : ℝ) ^ 2)) (stageGap M H h x a / (8 * (H : ℝ)))

/-- The low-gap threshold of (C.5); cardinalities and powers are real arithmetic. -/
noncomputable def lowGap (M : NominalMDP X A) (H : ℕ) : ℝ :=
  gapMin M H / (64 * (Fintype.card X : ℝ) * (Fintype.card A : ℝ) * (H : ℝ) ^ 3)

end CorruptRobustRL.Supervised.Supplement


