-- Prove2me | Definitions.Def_FoundationsRL_Structured_DEC
-- name    : FoundationsRL_Structured_DEC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:17:29.031483+00:00
-- url     : https://prove2.me/theorems/8b0f2b34-b0db-4f33-b9a8-579575821f2b
-- title:
--   The Decision-Estimation Coefficient game value (Eq. 4.15) and the DEC (Eq. 4.16)
-- statement:
--   This definition formalizes the **Decision-Estimation Coefficient** (DEC), the central
--   quantity of Chapter 4 (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, arXiv:2312.16730v1, Eqs. (4.15)-(4.16), pp. 64-65). Fix a
--   finite decision space $\Pi$, a function class $F \subseteq \mathbb{R}^\Pi$, and for each
--   $f \in F$ a maximizing decision $\pi_f = \arg\max_{\pi} f(\pi)$. At a reference model
--   $\hat f$ and scale $\gamma > 0$, the DEC game value is the min-max quantity
--
--   $$
--   \mathrm{dec}_\gamma(F, \hat f) := \min_{p \in \Delta(\Pi)} \max_{f \in F} \; \mathbb{E}_{\pi \sim p}\bigl[f(\pi_f) - f(\pi) - \gamma(f(\pi) - \hat f(\pi))^2\bigr],
--   $$
--
--   and the Decision-Estimation Coefficient of $F$ itself is
--
--   $$
--   \mathrm{dec}_\gamma(F) := \sup_{\hat f \in \mathrm{co}(F)} \mathrm{dec}_\gamma(F, \hat f),
--   $$
--
--   the sup taken over the convex hull of $F$ (Eq. (4.16)). `decGf F piStar γ fhat` is the
--   literal `sInf`-of-`sSup` transcription of the min-max game defining $\mathrm{dec}_\gamma(F,
--   \hat f)$ — the min over the probability simplex realized as `sInf` over the image of the
--   inner `sSup`-over-$F$ payoff — and `dec F piStar γ` is `sSup` of `decGf F piStar γ` over
--   `convexHull ℝ F`, matching Eq. (4.16) exactly. `piStar f` denotes $\pi_f$; callers supply
--   that `piStar` is indeed a maximizer of `f` on every `f ∈ F` where that fact is needed
--   (the definition itself does not constrain `piStar`).
--
--   **Formalization Note** This is deliberately the literal minimax quantity, not an opaque
--   free real number: the chapter's value is precisely that $\mathrm{dec}_\gamma(F)$ is later
--   *computed* exactly (Proposition 14) or bounded (Proposition 17) as this specific
--   quantity, so leaving it unconstrained would trivialize every downstream result.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eqs. (4.15)-(4.16), p. 65

import Mathlib

namespace FoundationsRL.Structured

/-- The value of the min-max game defining the Decision-Estimation Coefficient at a reference
model `fhat` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, Eq. (4.15), p. 65):

`decγ(F, f̂) := min_{p ∈ Δ(S)} max_{f ∈ F} E_{π∼p}[f(π_f) − f(π) − γ(f(π) − f̂(π))²]`.

`Π` is the (finite) decision space, `F` the function class, and `piStar f` denotes `π_f`, a
maximizer of `f` over `Π` (the book's `arg max`; callers supply that `piStar` is indeed
maximizing on every `f ∈ F` where that fact is needed). The min is realized as `sInf` over the
image, under `p`, of the `sSup` over `f ∈ F` of the payoff — a literal transcription of
`min_p max_f`, not an unconstrained bound. -/
noncomputable def decGf {S : Type*} [Fintype S] (F : Set (S → ℝ)) (piStar : (S → ℝ) → S)
    (γ : ℝ) (fhat : S → ℝ) : ℝ :=
  sInf ((fun p : S → ℝ =>
      sSup ((fun f : S → ℝ =>
          ∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) '' F))
    '' {p : S → ℝ | (∀ π, 0 ≤ p π) ∧ ∑ π, p π = 1})

/-- The Decision-Estimation Coefficient of the class `F` at scale `γ` (Eq. (4.16), p. 65):

`decγ(F) := sup_{f̂ ∈ co(F)} decγ(F, f̂)`. -/
noncomputable def dec {S : Type*} [Fintype S] (F : Set (S → ℝ)) (piStar : (S → ℝ) → S)
    (γ : ℝ) : ℝ :=
  sSup ((decGf F piStar γ) '' convexHull ℝ F)

end FoundationsRL.Structured


