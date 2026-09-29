-- Prove2me | Definitions.Def_FoundationsRL_GeneralDM_ConstrainedDEC
-- name    : FoundationsRL_GeneralDM_ConstrainedDEC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:22:13.827901+00:00
-- url     : https://prove2.me/theorems/e8f5f860-168a-499d-87c0-9c0af05ddcb9
-- title:
--   The constrained Decision-Estimation Coefficient (§6.5.1)
-- statement:
--   This bundle formalizes the **constrained Decision-Estimation Coefficient**, introduced to
--   prove lower bounds on regret (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, arXiv:2312.16730v1, §6.5.1, p. 97). For a radius $\varepsilon >
--   0$, model class $\mathcal{M}$ and reference model $\hat m$,
--   $$
--   \mathrm{dec}^c_\varepsilon(\mathcal{M}, \hat m) := \inf_{p \in \Delta(S)} \sup\Bigl\{
--     \mathbb{E}_{\pi \sim p}[f^m(\pi_m) - f^m(\pi)] \; : \; m \in \mathcal{M},\;
--     \mathbb{E}_{\pi \sim p}\bigl[D_H^2(m(\pi), \hat m(\pi))\bigr] \le \varepsilon^2 \Bigr\},
--   $$
--   with
--   $$
--   \mathrm{dec}^c_\varepsilon(\mathcal{M}) := \sup_{\hat m \in \mathrm{co}(\mathcal{M})}
--     \mathrm{dec}^c_\varepsilon(\mathcal{M} \cup \{\hat m\}, \hat m).
--   $$
--   Unlike the offset DEC, which subtracts the information gain, the constrained DEC places a
--   hard constraint on it.
--
--   `decCGf` is the literal transcription: for each $p$, the inner supremum ranges only over the
--   subset of $\mathcal{M}$ satisfying the information-gain constraint. `decC` takes the sup of
--   `decCGf` over the convex hull, playing the game at each $\hat m$ against the augmented class
--   $\mathcal{M} \cup \{\hat m\}$, exactly as the book's own definition.
--
--   **Formalization Note** The book adopts the convention (footnote 15, p. 97) that
--   $\mathrm{dec}^c_\varepsilon(\mathcal{M}, \hat m)$ is $0$ whenever some $p$ makes the
--   constrained subset of $\mathcal{M}$ empty. This literal transcription reproduces that
--   convention automatically: Lean's `sSup` of the image of an empty set is `0` on `ℝ`, and since
--   every other term of the outer `sInf` is nonnegative (the regret gap $f^m(\pi_m) - f^m(\pi)$ is
--   always $\ge 0$), the whole `sInf` is then exactly `0` whenever such a `p` exists.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.5.1, p. 97

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace FoundationsRL.GeneralDM

/-- The value of the constrained-minimax game defining the constrained Decision-Estimation
Coefficient at a reference model `mhat` and radius `ε` (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §6.5.1, p. 97):

`decc_ε(M, M̂) := inf_{p ∈ Δ(S)} sup { E_{π∼p}[f^M(π_M) − f^M(π)] : M ∈ 𝓜, E_{π∼p}[D²_H(M(π), M̂(π))] ≤ ε² }`.

The inner `sup` is realized as `sSup` over the image, under the payoff map, of the subset of `𝓜`
satisfying the information-gain constraint. Following the book's own footnote 15 convention that
`decc_ε(M, M̂)` is `0` whenever some `p` makes that constrained subset empty, and matching Lean's
convention that `sSup` of the image of an empty set is `0` on `ℝ`, this literal transcription
reproduces the footnote's convention automatically rather than needing to state it separately: at
such a `p`, the inner `sSup` defaults to `0`, and since every other term of the outer `sInf` is
`≥ 0` (the regret gap `f^M(π_M) − f^M(π)` is nonnegative), the whole `sInf` is then exactly `0`. -/
noncomputable def decCGf {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (ε : ℝ) (mhat : S → Y → ℝ) : ℝ :=
  sInf ((fun p : S → ℝ =>
      sSup ((fun m : S → Y → ℝ => ∑ π, p π * (fM rew m (piStar m) - fM rew m π)) ''
        {m ∈ 𝓜 | ∑ π, p π * hellingerSq (m π) (mhat π) ≤ ε ^ 2}))
    '' {p : S → ℝ | (∀ π, 0 ≤ p π) ∧ ∑ π, p π = 1})

/-- The constrained Decision-Estimation Coefficient of the class `𝓜` at radius `ε`
(Foster & Rakhlin, arXiv:2312.16730v1, §6.5.1, p. 97):

`decc_ε(M) := sup_{M̂ ∈ co(M)} decc_ε(M ∪ {M̂}, M̂)`,

the sup taken over the convex hull of `𝓜`; the constrained-DEC game at each `M̂` is played over the
augmented class `𝓜 ∪ {M̂}` (not `𝓜` alone), matching the book's own definition. -/
noncomputable def decC {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (ε : ℝ) : ℝ :=
  sSup ((fun mhat => decCGf (insert mhat 𝓜) rew piStar ε mhat) '' convexHull ℝ 𝓜)

end FoundationsRL.GeneralDM


