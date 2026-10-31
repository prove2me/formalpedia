-- Prove2me | Definitions.Def_FoundationsRL_LSVI_IsLowRank
-- name    : FoundationsRL_LSVI_IsLowRank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:21.77149+00:00
-- url     : https://prove2.me/theorems/dd0be158-fc66-4c78-a44e-6080d47df2ea
-- title:
--   The low-rank MDP class $\mathcal M$ of (7.3)
-- statement:
--   Fix a known feature map $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ and a horizon $H$. An episodic MDP $M$ is a **low-rank MDP** (it belongs to the class $\mathcal M$ of §7.2) if:
--
--   1. $\|\phi(s,a)\|_2\le1$ for all $(s,a)$;
--   2. there are unknown $\mu^M_h:\mathcal S\to\mathbb R^d$ and $w^M_h\in\mathbb R^d$ such that for every $h\in[H]$ and all $s,a,s'$
--   $$
--   P^M_h(s'\mid s,a)=\langle\phi(s,a),\mu^M_h(s')\rangle,\qquad \mathbb E[r_h\mid s,a]=\langle\phi(s,a),w^M_h\rangle,
--   $$
--   with $\|w^M_h\|_2\le\sqrt d$ and $\big\|\sum_{s'\in\mathcal S}|\mu^M_h(s')|\big\|_2\le\sqrt d$, where $|\cdot|$ is taken coordinatewise;
--   3. individual-step rewards lie in $[0,1]$: each $R^M_h(s,a)$ is supported on $[0,1]$;
--   4. cumulative rewards lie in $[0,1]$, in the form $Q^{M,\star}_h(s,a)\le1$ for every $h\in[H]$ and every $(s,a)$.
--
--   The factorization makes the transition matrix of rank at most $d$, so information is shared across states even when $\mathcal S$ and $\mathcal A$ are large or infinite; tabular MDPs are the case $d=|\mathcal S||\mathcal A|$, $\phi(s,a)=e_{s,a}$.
--
--   **Formalization Note** Condition 4 reads the book's "cumulative rewards are in $[0,1]$" from every state at every layer, as the proof of Lemma 28 uses it, and keeps only its expected-value consequence: an MDP whose cumulative reward lies in $[0,1]$ almost surely from every state satisfies it. Each coordinate series $\sum_{s'}|\mu^M_h(s')_j|$ is required to converge, which the norm bound presupposes.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (7.3), pp. 131–132, with the standing assumptions of p. 129 and p. 132

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP

open MeasureTheory

namespace FoundationsRL.LSVI

/-- The low-rank MDP class `𝓜` of §7.2 (Foster & Rakhlin, *Foundations of Reinforcement Learning
and Interactive Decision Making*, arXiv:2312.16730v1, (7.3), pp. 131–132, with the standing
assumptions of p. 129 and p. 132), for a known feature map `ϕ : S × A → ℝ^d` and horizon `H`.

1. `feature_norm`: `ϕ(s, a) ∈ B^d_2(1)`;
2. `factor`: there are unknown `μ^M_h : S → ℝ^d` and `w^M_h ∈ ℝ^d` with, for every `h ∈ [H]`,
   `P^M_h(s' | s, a) = ⟨ϕ(s, a), μ^M_h(s')⟩`, `E[r_h | s, a] = ⟨ϕ(s, a), w^M_h⟩`,
   `w^M_h ∈ B^d_2(√d)` and `‖Σ_{s'∈S} |μ^M_h(s')|‖ ≤ √d`, where `|μ^M_h(s')|` is the
   coordinatewise absolute value;
3. `reward_mem`: individual-step rewards are in `[0, 1]`: `R^M_h(s, a)` is supported on `[0, 1]`;
4. `cumulative`: cumulative rewards are in `[0, 1]`, in the form the analysis uses (proof of
   Lemma 28, p. 137): `Q^{M,⋆}_h(s, a) ≤ 1` for every `h ∈ [H]` and every `(s, a)`.

**Formalization Note.** The sum `Σ_{s'} |μ^M_h(s')|` is a vector of coordinatewise series; each
is required to converge, which the book's `‖·‖ ≤ √d` presupposes. Condition 4 is the book's
"cumulative rewards in `[0, 1]`" read from every state at every layer, as the proof of Lemma 28
uses it, and only in expectation (`Q^{M,⋆}_h` is the maximal expected reward-to-go); an MDP
whose cumulative reward lies in `[0, 1]` almost surely from every state satisfies it. -/
structure IsLowRank {S A : Type*} {d : ℕ} (M : EpisodicMDP S A) (H : ℕ)
    (ϕ : S → A → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- `ϕ(s, a) ∈ B^d_2(1)`. -/
  feature_norm : ∀ s a, ‖ϕ s a‖ ≤ 1
  /-- The low-rank factorization (7.3) with its norm bounds. -/
  factor : ∃ (μ : ℕ → S → EuclideanSpace ℝ (Fin d)) (w : ℕ → EuclideanSpace ℝ (Fin d)),
    ∀ h ∈ Finset.Icc 1 H,
      (∀ s a s', (M.P h s a s').toReal = inner ℝ (ϕ s a) (μ h s')) ∧
      (∀ s a, M.meanReward h s a = inner ℝ (ϕ s a) (w h)) ∧
      ‖w h‖ ≤ Real.sqrt d ∧
      (∀ j, Summable fun s' => |μ h s' j|) ∧
      ‖(WithLp.toLp 2 (fun j => ∑' s', |μ h s' j|) : EuclideanSpace ℝ (Fin d))‖ ≤ Real.sqrt d
  /-- Individual-step rewards lie in `[0, 1]` almost surely. -/
  reward_mem : ∀ h ∈ Finset.Icc 1 H, ∀ s a, M.R h s a (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- Cumulative rewards lie in `[0, 1]`: `Q^{M,⋆}_h ≤ 1` at every layer. -/
  cumulative : ∀ h ∈ Finset.Icc 1 H, ∀ s a, M.Qstar H h s a ≤ 1

end FoundationsRL.LSVI


