-- Prove2me | Definitions.Def_OptimisticPSRL_Diameter_Setting
-- name    : OptimisticPSRL_Diameter_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:50.52298+00:00
-- url     : https://prove2.me/theorems/673afa35-0b76-4c28-a2f8-82ac056e2e9f
-- title:
--   §3, p. 5 and Lemma 5.6, p. 12 — the extended MDP M̃ built from sample vectors Q^j_{s,a}, and the minimum expected times E^s
-- statement:
--   This file fixes the two objects of Agrawal and Jia's Lemma 5.6 that are not already part of the published finite-MDP library (`FiniteMDPLearning`): the extended MDP built from sampled transition vectors, and the vector of minimum expected travel times to a target state.
--
--   Let $\mathcal M$ be a finite MDP with states $\mathcal S=\{1,\dots,S\}$, actions $\mathcal A=\{1,\dots,A\}$, transition probability vectors $P_{s,a}\in\Delta^{S}$ and rewards $r_{s,a}\in[0,1]$.
--
--   1. **Extended MDP (§3, p. 5).** Suppose that for every state $s$ and action $a$ we are given $\psi$ probability vectors $Q^{1}_{s,a},\dots,Q^{\psi}_{s,a}\in\Delta^{S}$ (the paper's sampled vectors $Q^{j,k}_{s,a}$ of epoch $k$; the epoch plays no role here). The extended MDP $\tilde{\mathcal M}$ has the same states and, for every action $a$, the $\psi$ actions $a^{1},\dots,a^{\psi}$. Taking $a^{j}$ in state $s$ yields the reward $r_{s,a}$, and the next state is drawn from $Q^{j}_{s,a}$:
--   $$\tilde P_{s,a^{j}} = Q^{j}_{s,a},\qquad \tilde r_{s,a^{j}} = r_{s,a}.$$
--
--   2. **Minimum expected travel times (Lemma 5.6, p. 12).** For a target state $s$, the vector $E^{s}\in[0,\infty]^{S}$ has entries
--   $$E^{s}_{s'} = \min_{\pi:\mathcal S\to\mathcal A} T^{\pi}_{s'\to s},$$
--   where $T^{\pi}_{s'\to s}$ is the expected number of steps the deterministic stationary policy $\pi$ takes to reach $s$ from $s'$ (Definition 2, p. 3). In particular $E^{s}_{s}=0$.
--
--   The file also records that the transition row and the reward of the action $a^{j}$ in $\tilde{\mathcal M}$ are $Q^{j}_{s,a}$ and $r_{s,a}$. These objects are what Lemma 5.6 is about: the diameter of $\tilde{\mathcal M}$ is controlled by that of $\mathcal M$ when, for every target, every state-action pair has some sample that is optimistic with respect to $E^{s}$.
--
--   **Formalization Note.** States, actions and samples are 0-based: `Fin S`, `Fin A`, `Fin ψ`. The extended action $a^{j}$ is the element `finProdFinEquiv (a, j)` of `Fin (A * ψ)` (named `extendedAction a j`); conversely an action `k` of the extended MDP is read as the pair `finProdFinEquiv.symm k`. The sample vectors are arbitrary probability vectors with values in $\mathbb R_{\ge 0}$ summing to one; nothing else (in particular no positivity, no Dirichlet law) is assumed. `minTravel M tgt src` is the infimum over all `f : Fin S → Fin A` of the platform's `mdpTravelTime M f src tgt`, valued in $[0,\infty]$; when $A=0$ and $S\ge1$ there is no policy and the empty infimum is $\infty$.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 5, §3 Extended MDP; p. 12, Lemma 5.6 (definition of E^s)

import Mathlib
import Definitions.Def_FiniteMDPLearning

namespace OptimisticPSRL.Diameter

open BanditAlgorithm NNReal ENNReal

/-- The action `a^j` of the extended MDP (Agrawal–Jia §3, p. 5): the copy of action
`a : Fin A` that uses sample `j : Fin ψ`, encoded in `Fin (A * ψ)` through
`finProdFinEquiv : Fin A × Fin ψ ≃ Fin (A * ψ)`. -/
def extendedAction {A ψ : ℕ} (a : Fin A) (j : Fin ψ) : Fin (A * ψ) :=
  finProdFinEquiv (a, j)

/-- The extended MDP `M̃` of Agrawal–Jia §3, p. 5. Given sampled probability vectors
`Q s a j : Fin S → ℝ≥0` (`j = 0, …, ψ − 1`, the paper's `Q^j_{s,a}`, `j = 1, …, ψ`),
every action `a` of `M` is replaced by `ψ` actions `a^j`. On taking `a^j` in state `s`
the reward is `r_{s,a}` but the next state is drawn from `Q^j_{s,a}`. The action
`k : Fin (A * ψ)` is read as the pair `(a, j) = finProdFinEquiv.symm k`. -/
noncomputable def extendedMDP {S A ψ : ℕ} (M : FiniteMDP S A)
    (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0)
    (hQ : ∀ s a j, ∑ i, Q s a j i = 1) : FiniteMDP S (A * ψ) where
  P s k := Q s (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  P_sum_one s _ := hQ s _ _
  r s k := M.r s (finProdFinEquiv.symm k).1
  r_mem_Icc s _ := M.r_mem_Icc s _

/-- The vector `E^s` of Lemma 5.6 (p. 12) with `s = tgt`: its entry at `src` is the
minimum, over deterministic memoryless policies `f : Fin S → Fin A`, of the expected
number of steps to reach `tgt` from `src` in `M`, `E^{tgt}_{src} = min_π T^π_{src→tgt}`.
Valued in `[0, ∞]`; `minTravel M tgt tgt = 0`. -/
noncomputable def minTravel {S A : ℕ} (M : FiniteMDP S A) (tgt : Fin S) :
    Fin S → ℝ≥0∞ :=
  fun src => ⨅ f : Fin S → Fin A, mdpTravelTime M f src tgt

/-- The transition row of `a^j` in the extended MDP is the sample `Q^j_{s,a}`. -/
@[simp] lemma extendedMDP_P_extendedAction {S A ψ : ℕ} (M : FiniteMDP S A)
    (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0) (hQ : ∀ s a j, ∑ i, Q s a j i = 1)
    (s : Fin S) (a : Fin A) (j : Fin ψ) :
    (extendedMDP M Q hQ).P s (extendedAction a j) = Q s a j := by
  show Q s (finProdFinEquiv.symm (finProdFinEquiv (a, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a, j))).2 = Q s a j
  rw [Equiv.symm_apply_apply]

/-- The reward of `a^j` in the extended MDP is `r_{s,a}`. -/
@[simp] lemma extendedMDP_r_extendedAction {S A ψ : ℕ} (M : FiniteMDP S A)
    (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0) (hQ : ∀ s a j, ∑ i, Q s a j i = 1)
    (s : Fin S) (a : Fin A) (j : Fin ψ) :
    (extendedMDP M Q hQ).r s (extendedAction a j) = M.r s a := by
  show M.r s (finProdFinEquiv.symm (finProdFinEquiv (a, j))).1 = M.r s a
  rw [Equiv.symm_apply_apply]

end OptimisticPSRL.Diameter


