-- Prove2me | Definitions.Def_StatComplexityDM_TabularPS_MDP
-- name    : StatComplexityDM_TabularPS_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:32.870541+00:00
-- url     : https://prove2.me/theorems/27af14cd-4c0d-4fd1-94f1-6d73fe46cfe3
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
--   The model satisfies the standing reward convention of §5.2 when each reward outcome lies in $[0,1]$ and, under every randomized policy, every trajectory of positive probability has total reward $\sum_{h=1}^H r_h\in[0,1]$. The file also defines backward state and action values and the occupancy-weighted local Hellinger and total-variation discrepancies used in the appendix lemmas.
--
--   **Formalization Note** The representation uses finite alphabets and zero-based `Fin H` layers. The last transition leads to a deterministic terminal state, so it does not enter a trajectory or local divergence. `RewardsNormalized` combines the paper's reward alphabet $[0,1]$ with its almost-sure total-reward bound $\sum_h r_h\in[0,1]$. The initial distribution and the horizon condition $H\ge1$ are hypotheses of the theorem items that use this file.
-- source:
--   arXiv:2112.13487v3, Example 1.2, p. 6; §2, p. 10; §5.2, p. 33; Lemmas F.1–F.3, pp. 106–107

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.TabularPS

open FoundationsRL.GeneralDM

/-- An episodic, nonstationary MDP with transition and reward kernels.  The last
transition is to a deterministic terminal state and is ignored by `trajLaw`. -/
structure TabMDP (S A W : Type*) (H : ℕ) where
  P : Fin H → S → A → S → ℝ
  R : Fin H → S → A → W → ℝ

/-- All kernels of a tabular MDP are probability vectors. -/
def IsTabMDP {S A W : Type*} [Fintype S] [Fintype W] {H : ℕ}
    (M : TabMDP S A W H) : Prop :=
  (∀ h s a, StatComplexityDM.LowerBound.IsDist (M.P h s a)) ∧ (∀ h s a, StatComplexityDM.LowerBound.IsDist (M.R h s a))

/-- A randomized, nonstationary Markov policy. -/
abbrev Policy (S A : Type*) (H : ℕ) := Fin H → S → A → ℝ

def IsPolicy {S A : Type*} [Fintype A] {H : ℕ}
    (π : Policy S A H) : Prop := ∀ h s, StatComplexityDM.LowerBound.IsDist (π h s)

/-- The recorded state, action, reward-outcome history. -/
abbrev Traj (S A W : Type*) (H : ℕ) := Fin H → S × A × W

/-- The terminal transition has weight one. -/
def nextWeight {S A W : Type*} {H : ℕ} (M : TabMDP S A W H)
    (τ : Traj S A W H) (h : Fin H) : ℝ :=
  if hn : h.val + 1 < H then
    M.P h (τ h).1 (τ h).2.1 (τ ⟨h.val + 1, hn⟩).1
  else 1

/-- The finite trajectory law under a shared initial distribution `d1`. -/
noncomputable def trajLaw {S A W : Type*} {H : ℕ}
    (d1 : S → ℝ) (M : TabMDP S A W H) (π : Policy S A H)
    (τ : Traj S A W H) : ℝ :=
  ∏ h : Fin H,
    (if h.val = 0 then d1 (τ h).1 else 1) *
      π h (τ h).1 (τ h).2.1 *
      M.R h (τ h).1 (τ h).2.1 (τ h).2.2 * nextWeight M τ h

/-- The standing reward convention of §5.2: individual rewards lie in `[0,1]`,
and under every randomized policy the total reward `∑ h, r_h` of every trajectory
of positive probability lies in `[0,1]` almost surely. -/
def RewardsNormalized {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (M : TabMDP S A W H) : Prop :=
  (∀ w, 0 ≤ rv w ∧ rv w ≤ 1) ∧
    ∀ π τ, IsPolicy π → trajLaw d1 M π τ ≠ 0 →
      0 ≤ ∑ h : Fin H, rv (τ h).2.2 ∧
        ∑ h : Fin H, rv (τ h).2.2 ≤ 1

/-- Expected cumulative reward of a policy. -/
noncomputable def value {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (M : TabMDP S A W H)
    (π : Policy S A H) : ℝ :=
  ∑ τ : Traj S A W H, trajLaw d1 M π τ * ∑ h : Fin H, rv (τ h).2.2

/-- The probability of a state-action pair at layer `h`. -/
noncomputable def occ {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H)
    (π : Policy S A H) (h : Fin H) (s : S) (a : A) : ℝ := by
  classical
  exact ∑ τ : Traj S A W H,
    if (τ h).1 = s ∧ (τ h).2.1 = a then trajLaw d1 M π τ else 0

/-- The reward kernel's mean at a state-action pair. -/
noncomputable def meanReward {S A W : Type*} [Fintype W] {H : ℕ}
    (rv : W → ℝ) (M : TabMDP S A W H) (h : Fin H) (s : S) (a : A) : ℝ :=
  ∑ w, M.R h s a w * rv w

/-- Backward recursion, with zero value after the final layer. -/
noncomputable def Vremaining {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (rv : W → ℝ) (M : TabMDP S A W H) (π : Policy S A H) :
    ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s =>
      if hh : H - (n + 1) < H then
        ∑ a, π ⟨H - (n + 1), hh⟩ s a *
          (meanReward rv M ⟨H - (n + 1), hh⟩ s a +
            if H - (n + 1) + 1 < H then
              ∑ s', M.P ⟨H - (n + 1), hh⟩ s a s' * Vremaining rv M π n s'
            else 0)
      else 0

/-- State value from layer `h`; `Vfun … H s = 0`. -/
noncomputable def Vfun {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (rv : W → ℝ) (M : TabMDP S A W H) (π : Policy S A H)
    (h : ℕ) (s : S) : ℝ := Vremaining rv M π (H - h) s

/-- State-action value with the terminal continuation set to zero. -/
noncomputable def Qfun {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (rv : W → ℝ) (M : TabMDP S A W H) (π : Policy S A H)
    (h : Fin H) (s : S) (a : A) : ℝ :=
  meanReward rv M h s a +
    if h.val + 1 < H then
      ∑ s', M.P h s a s' * Vfun rv M π (h.val + 1) s'
    else 0

/-- Squared Hellinger discrepancy of the one-step kernels. -/
noncomputable def localHellinger {S A W : Type*} [Fintype S] [Fintype W]
    {H : ℕ} (M Mbar : TabMDP S A W H) (h : Fin H) (s : S) (a : A) : ℝ :=
  (if h.val + 1 < H then hellingerSq (M.P h s a) (Mbar.P h s a) else 0) +
    hellingerSq (M.R h s a) (Mbar.R h s a)

/-- Total-variation discrepancy of the one-step kernels. -/
noncomputable def localTV {S A W : Type*} [Fintype S] [Fintype W]
    {H : ℕ} (M Mbar : TabMDP S A W H) (h : Fin H) (s : S) (a : A) : ℝ :=
  (if h.val + 1 < H then totalVariationDiscrete (M.P h s a) (Mbar.P h s a) else 0) +
    totalVariationDiscrete (M.R h s a) (Mbar.R h s a)

/-- The occupancy-weighted sum of local divergences. -/
noncomputable def expectedLocalHellinger {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] {H : ℕ}
    (d1 : S → ℝ) (M Mbar : TabMDP S A W H) (π : Policy S A H) : ℝ :=
  ∑ h : Fin H, ∑ s, ∑ a, occ d1 Mbar π h s a * localHellinger M Mbar h s a

/-- The occupancy-weighted sum of local total-variation distances. -/
noncomputable def expectedLocalTV {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] {H : ℕ}
    (d1 : S → ℝ) (M Mbar : TabMDP S A W H) (π : Policy S A H) : ℝ :=
  ∑ h : Fin H, ∑ s, ∑ a, occ d1 Mbar π h s a * localTV M Mbar h s a

/-- The sum of the squared local total-variation distances used in the
posterior-sampling decoupling inequality. -/
noncomputable def localTVSq {S A W : Type*} [Fintype S] [Fintype W]
    {H : ℕ} (M Mbar : TabMDP S A W H) (h : Fin H) (s : S) (a : A) : ℝ :=
  (if h.val + 1 < H then (totalVariationDiscrete (M.P h s a) (Mbar.P h s a)) ^ 2 else 0) +
    (totalVariationDiscrete (M.R h s a) (Mbar.R h s a)) ^ 2

noncomputable def expectedLocalTVSq {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] {H : ℕ}
    (d1 : S → ℝ) (M Mbar : TabMDP S A W H) (π : Policy S A H) : ℝ :=
  ∑ h : Fin H, ∑ s, ∑ a, occ d1 Mbar π h s a * localTVSq M Mbar h s a

end StatComplexityDM.TabularPS


