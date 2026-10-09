-- Prove2me | Definitions.Def_RegLearnGames_FirstOrder_Setting
-- name    : RegLearnGames_FirstOrder_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:51.818066+00:00
-- url     : https://prove2.me/theorems/416d823e-c406-4c8c-8852-4c0d10c79f1c
-- title:
--   Appendix H, supp. p. 10 — finite cost game, social cost, pure optimum, cost vectors, smoothness, and first-order regret
-- statement:
--   Let $n$ players each have $d$ pure strategies. A pure profile is $s=(s_i)_i$ and a mixed profile $w=(w_i)_i$ consists of independent distributions over the players' strategy sets. Player $i$ has a cost $c_i(s)$.
--
--   The total cost of a pure profile and its expected value under a mixed profile are
--   $$C(s)=\sum_i c_i(s),\qquad C(w)=\mathbb E_{s\sim w}[C(s)].$$
--   When $d\ge1$, the pure optimum is $\mathrm{OPT}'=\min_s C(s)$. The cost vector against opponents' mixed strategies has coordinate $c_{i,x}(w)=\mathbb E_{s_{-i}\sim w_{-i}}[c_i(x,s_{-i})]$.
--
--   The cost game is **$(\lambda,\mu)$-smooth** when one pure profile $s^*$ satisfies
--   $$\sum_i c_i(s_i^*,s_{-i})\le\lambda\mathrm{OPT}'+\mu C(s)\qquad\text{for every pure profile }s.$$
--   A trajectory $w^1,\ldots,w^T$ has the **first-order regret bound** with constants $A_1,A_2$ when, for every player $i$ and every fixed pure strategy $x$,
--   $$\sum_{t=1}^T\langle w_i^t,c_i^t\rangle-\sum_{t=1}^T c_{i,x}^t\le A_1\sqrt{\log d\sum_{t=1}^T c_{i,x}^t}+A_2\log d.$$
--
--   These definitions supply the common cost model for Theorem 23 and its proof milestones.
--
--   **Formalization Note** Players and strategies are indexed from zero by `Fin n` and `Fin d`. Time retains the paper's indices $1,\ldots,T$. The published `AGT.profileProb` and `AGT.expectedPayoff` definitions give expectations under independent mixed play; although their name uses “payoff,” the latter is simply an expectation and is used here for costs. The pure optimum uses a finite minimum with $d\ge1$. The regret predicate describes the realized trajectory at horizon $T$; an algorithm guaranteeing equation (21) on every sequence supplies this predicate on its realized play.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), Appendix H, equations (20)–(21); game model p. 2

import Mathlib
import Definitions.Def_agt_games

namespace RegLearnGames.FirstOrder

open Finset

/-- Total cost of a pure strategy profile, Appendix H, p. 10. -/
def socialCostPure {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (s : Fin n → Fin d) : ℝ :=
  ∑ i, c i s

/-- Expected total cost when players randomize independently. -/
def socialCost {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) : ℝ :=
  ∑ s, AGT.profileProb w s * socialCostPure c s

/-- The minimum total cost among pure strategy profiles. -/
def optCost {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (socialCostPure c)

/-- The expected cost of playing `x` against the other players' mixed strategies. -/
def costVec {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) (i : Fin n) (x : Fin d) : ℝ :=
  AGT.expectedPayoff c (Function.update w i (Pi.single x 1)) i

/-- Smoothness of the cost game in equation (20), witnessed by one pure profile. -/
def IsSmoothCost {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ) (lam mu : ℝ) : Prop :=
  ∃ sstar : Fin n → Fin d, ∀ s : Fin n → Fin d,
    (∑ i, c i (Function.update s i (sstar i))) ≤
      lam * optCost c + mu * socialCostPure c s

/-- Equation (21) on a realized sequence, for every player and pure comparator. -/
def HasFirstOrderRegret {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ) (A₁ A₂ : ℝ) : Prop :=
  ∀ (i : Fin n) (x : Fin d),
    (∑ t ∈ Finset.Icc 1 T, (w t i) ⬝ᵥ (costVec c (w t) i)) -
        (∑ t ∈ Finset.Icc 1 T, costVec c (w t) i x) ≤
      A₁ * Real.sqrt (Real.log (d : ℝ) *
        (∑ t ∈ Finset.Icc 1 T, costVec c (w t) i x)) +
        A₂ * Real.log (d : ℝ)

end RegLearnGames.FirstOrder


