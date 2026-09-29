-- Prove2me | Definitions.Def_FoundationsRL_GeneralDM_DEC
-- name    : FoundationsRL_GeneralDM_DEC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:21:20.935979+00:00
-- url     : https://prove2.me/theorems/392b4023-ebdd-4231-a04e-4cc75f583d65
-- title:
--   The general (offset) Decision-Estimation Coefficient (Eqs. 6.9-6.10)
-- statement:
--   This bundle formalizes the **general Decision-Estimation Coefficient (DEC)**, the central
--   complexity measure of Chapter 6 (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, arXiv:2312.16730v1, Eqs. (6.9)-(6.10), p. 97). Fix a finite
--   decision space $S$, finite outcome type $Y$, a model class $\mathcal{M} \subseteq (S \to (Y
--   \to \mathbb{R}))$, reward-extraction map $\mathrm{rew}$, and for each model $m$ a maximizing
--   decision $\pi_m = \arg\max_\pi f^m(\pi)$. At a reference model $\hat m$ and scale $\gamma >
--   0$, the DEC game value is
--   $$
--   \mathrm{dec}_\gamma(\mathcal{M}, \hat m) := \inf_{p \in \Delta(S)} \sup_{m \in \mathcal{M}}
--     \mathbb{E}_{\pi \sim p}\bigl[f^m(\pi_m) - f^m(\pi) - \gamma \cdot D_H^2(m(\pi), \hat m(\pi))\bigr],
--   $$
--   and the Decision-Estimation Coefficient of $\mathcal{M}$ itself is
--   $$
--   \mathrm{dec}_\gamma(\mathcal{M}) := \sup_{\hat m \in \mathrm{co}(\mathcal{M})} \mathrm{dec}_\gamma(\mathcal{M}, \hat m),
--   $$
--   the sup taken over the convex hull of $\mathcal{M}$ (Eq. (6.10)).
--
--   `decGf 𝓜 rew piStar γ mhat` is the literal `sInf`-of-`sSup` transcription of the min-max game
--   defining $\mathrm{dec}_\gamma(\mathcal{M}, \hat m)$, and `dec 𝓜 rew piStar γ` is `sSup` of
--   `decGf` over `convexHull ℝ 𝓜`, matching Eq. (6.10) exactly. `piStar m` denotes $\pi_m$;
--   callers supply that `piStar` is indeed a maximizer of `fM rew m` where that fact is needed.
--
--   **Formalization Note** This is the same literal minimax pattern used for the DEC of Chapter 4
--   (this series' `Structured.DEC`, not imported here since draft items cannot import other
--   chunks' drafts), extended with the information-gain term measured in squared Hellinger
--   distance between full outcome distributions rather than squared error between mean rewards —
--   the substantive generalization Chapter 6 makes.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eqs. (6.9)-(6.10), p. 97

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace FoundationsRL.GeneralDM

/-- The value of the min-max game defining the (general, offset) Decision-Estimation Coefficient
at a reference model `mhat` (Foster & Rakhlin, *Foundations of Reinforcement Learning and
Interactive Decision Making*, arXiv:2312.16730v1, Eq. (6.9), p. 97):

`decγ(M, M̂) := inf_{p ∈ Δ(S)} sup_{M ∈ 𝓜} E_{π∼p}[f^M(π_M) − f^M(π) − γ · D²_H(M(π), M̂(π))]`.

`S` is the (finite) decision space, `Y` the finite outcome (reward, observation) alphabet, `𝓜` the
model class, `rew` the reward-extraction map used by `fM`, and `piStar m` denotes `π_m`, a
maximizer of `fM rew m` over `S` (the book's `arg max`; callers supply that `piStar` is indeed
maximizing on every `m` where that fact is needed). The inf is realized as `sInf` over the image,
under `p`, of the `sSup` over `m ∈ 𝓜` of the payoff — a literal transcription of `inf_p sup_M`, not
an unconstrained bound. -/
noncomputable def decGf {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (γ : ℝ) (mhat : S → Y → ℝ) : ℝ :=
  sInf ((fun p : S → ℝ =>
      sSup ((fun m : S → Y → ℝ =>
          ∑ π, p π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat π))) '' 𝓜))
    '' {p : S → ℝ | (∀ π, 0 ≤ p π) ∧ ∑ π, p π = 1})

/-- The (general, offset) Decision-Estimation Coefficient of the class `𝓜` at scale `γ`
(Foster & Rakhlin, arXiv:2312.16730v1, Eq. (6.10), p. 97): `decγ(M) := sup_{M̂ ∈ co(M)} decγ(M, M̂)`,
the sup taken over the convex hull of `𝓜`. -/
noncomputable def dec {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (γ : ℝ) : ℝ :=
  sSup ((decGf 𝓜 rew piStar γ) '' convexHull ℝ 𝓜)

end FoundationsRL.GeneralDM


