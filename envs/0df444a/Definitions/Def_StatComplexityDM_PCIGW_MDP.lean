-- Prove2me | Definitions.Def_StatComplexityDM_PCIGW_MDP
-- name    : StatComplexityDM_PCIGW_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:53.117404+00:00
-- url     : https://prove2.me/theorems/a445c1b8-7802-45b7-8215-b33b2cc2b7ca
-- title:
--   Example 1.2 and §5.2 — tabular MDPs, trajectory laws, values, occupancy, and local divergences
-- statement:
--   A tabular model has a finite state set $S$, action set $A$, horizon $H\ge1$, and finite reward alphabet $W$. At each layer $h$, state $s$, and action $a$, it specifies a transition probability vector $P_h(\cdot\mid s,a)$ and a reward probability vector $R_h(\cdot\mid s,a)$. A randomized nonstationary policy specifies a probability vector $\pi_h(\cdot\mid s)$. All models share an initial distribution $d_1$.
--
--   The trajectory law multiplies the initial, policy, reward, and nonterminal transition probabilities. For a reward map $r:W\to\mathbb R$, the policy value and layer occupancy are
--   $$
--   f^M(\pi)=\mathbb E^{M,\pi}\!\left[\sum_{h=1}^{H}r_h\right],\qquad
--   d_h^{M,\pi}(s,a)=\Pr^{M,\pi}(s_h=s,a_h=a).
--   $$
--   The model satisfies the standing normalization of §5.2 when, under every randomized policy, every trajectory of positive probability has total reward $\sum_{h=1}^H r_h\in[0,1]$. The file also defines backward state and action values and the occupancy-weighted local Hellinger and total-variation discrepancies used in the appendix lemmas.
--
--   **Formalization Note** The representation uses finite alphabets and zero-based `Fin H` layers. The last transition leads to a deterministic terminal state, so it does not enter a trajectory or local divergence. `RewardsNormalized` is exactly the paper's almost-sure total-reward bound $\sum_h r_h\in[0,1]$; no sign or range condition is placed on individual per-step rewards.
-- source:
--   arXiv:2112.13487v3, Example 1.2, p. 6; §2, p. 10; §5.2, p. 33; Lemmas F.1–F.3, pp. 106–107

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_TabularPS_MDP

namespace StatComplexityDM.PCIGW

open FoundationsRL.GeneralDM

/-- The paper's almost-sure bound on total episode reward, without an
additional per-stage sign convention. -/
def EpisodeRewardsNormalized {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (M : StatComplexityDM.TabularPS.TabMDP S A W H) : Prop :=
  ∀ π τ, StatComplexityDM.TabularPS.IsPolicy π → StatComplexityDM.TabularPS.trajLaw d1 M π τ ≠ 0 →
    0 ≤ ∑ h : Fin H, rv (τ h).2.2 ∧
      ∑ h : Fin H, rv (τ h).2.2 ≤ 1

/-- The weight of the suffix of a trajectory starting at layer `k`, conditional
on its first state.  It is used only to state supportwise reward bounds. -/
noncomputable def suffixWeight {S A W : Type*} {H : ℕ}
    (M : StatComplexityDM.TabularPS.TabMDP S A W H) (π : StatComplexityDM.TabularPS.Policy S A H) (k : Fin H)
    (τ : StatComplexityDM.TabularPS.Traj S A W H) : ℝ :=
  ∏ h ∈ (Finset.univ.filter (fun h : Fin H => k.val ≤ h.val)),
    π h (τ h).1 (τ h).2.1 * M.R h (τ h).1 (τ h).2.1 (τ h).2.2 *
      StatComplexityDM.TabularPS.nextWeight M τ h

/-- Total reward is in `[0,1]` on every supported trajectory and on every
supported suffix started from an arbitrary state. The suffix clause is the
explicit uniform-start convention needed in the local simulation lemma. -/
def RewardsNormalized {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (M : StatComplexityDM.TabularPS.TabMDP S A W H) : Prop :=
  (∀ w, 0 ≤ rv w ∧ rv w ≤ 1) ∧
  EpisodeRewardsNormalized d1 rv M ∧
  (∀ π k τ, StatComplexityDM.TabularPS.IsPolicy π → suffixWeight M π k τ ≠ 0 →
    ∑ h ∈ (Finset.univ.filter (fun h : Fin H => k.val ≤ h.val)),
      rv (τ h).2.2 ≤ 1)

end StatComplexityDM.PCIGW


