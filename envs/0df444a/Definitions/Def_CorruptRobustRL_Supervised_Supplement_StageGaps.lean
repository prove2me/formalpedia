-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_StageGaps
-- name    : CorruptRobustRL_Supervised_Supplement_StageGaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:07:11.724614+00:00
-- url     : https://prove2.me/theorems/70ea0318-36e0-47a5-9392-8b1704f8c864
-- title:
--   Stage gaps and the minimum strictly positive stage gap
-- statement:
--   Let $M$ be a finite nominal MDP, $H$ its horizon and $V_h^\star,Q_h^\star$ its published optimal values. For each stage $h$, state $x$ and action $a$, set
--   $$g_h(x,a)=V_h^\star(x)-Q_h^\star(x,a),\qquad g_{\min}=\min\{g_h(x,a):h\in[H],\ x\in\mathcal X,\ a\in\mathcal A,\ g_h(x,a)>0\}.$$
--   The finite set of positive gaps is computed from the model. Its minimum is used only when it is nonempty; when every action is optimal at every stage, the total definition returns zero. This retains the all-optimal, zero-loss case, including tied optimal actions.
--
--   These gaps determine the clipping thresholds of the refined decomposition. The strictly positive stage-gap convention is explicit in the proof on printed p. 69. Printed p. 8 writes the minimum non-zero gap through the per-pair gap $\min_h g_h(x,a)$; that reading is not used, because it can exceed a positive stage gap and the clipped decompositions then fail. **Formalization Note** Stages use the published zero-based indexing, so Lean stage $h$ represents paper stage $h+1$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, pp. 8, 69; stage gaps and the proof of Lemma E.4

import Definitions.Def_CorruptRobustRL_Supervised_MDP

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X] [Fintype A] [Nonempty A]

/-- Stage gap, p. 8, evaluated only at h < H by the results. -/
noncomputable def stageGap (M : NominalMDP X A) (H h : ℕ) (x : X) (a : A) : ℝ :=
  Vstar M H h x - Qstar M H h x a

/-- All strictly positive stage gaps, as in the proof on p. 69. -/
noncomputable def positiveGaps (M : NominalMDP X A) (H : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ.image (fun z : Fin H × X × A =>
    stageGap M H z.1 z.2.1 z.2.2)).filter (fun g => 0 < g)

/-- Minimum strictly positive stage gap; 0 if every action is optimal at every stage.
This convention retains the zero-loss case without requiring a positive gap. -/
noncomputable def gapMin (M : NominalMDP X A) (H : ℕ) : ℝ :=
  if h : (positiveGaps M H).Nonempty then (positiveGaps M H).min' h else 0

end CorruptRobustRL.Supervised.Supplement


