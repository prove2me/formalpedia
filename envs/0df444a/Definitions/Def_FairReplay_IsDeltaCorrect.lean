-- Prove2me | Definitions.Def_FairReplay_IsDeltaCorrect
-- name    : FairReplay_IsDeltaCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:24.902192+00:00
-- url     : https://prove2.me/theorems/037553a6-6f2d-490a-a1ef-e274dd496c9c
-- title:
--   $\delta$-correct sequential tester
-- statement:
--   A **sequential tester** for a null environment $\nu_0$ against an alternative $\nu_1$ (on the same actions) is a triple $(\pi,\tau,\psi)$:
--
--   1. an adaptive, possibly randomized policy $\pi$ choosing each round's action from the past transcript;
--   2. a stopping time $\tau\in\{0,1,2,\dots\}\cup\{\infty\}$ of the transcript filtration ($\tau=\infty$ means the tester never stops);
--   3. a decision $\psi$, with $\psi=\text{true}$ meaning "reject $H_0$".
--
--   The tester is **$\delta$-correct** if
--
--   $$
--   \mathbb P_{\nu_0}\bigl(\tau<\infty,\ \psi=\text{reject}\bigr)\le\delta
--   \quad\text{and}\quad
--   \mathbb P_{\nu_1}\bigl(\text{not }(\tau<\infty\text{ and }\psi=\text{reject})\bigr)\le\delta .
--   $$
--
--   **Formalization Note** A run that never stops counts as an error under the alternative, so the tester that never stops is not $\delta$-correct for $\delta<1$. Measurability of $\psi$ for the stopped σ-algebra is imposed where testers are quantified.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4, p.14 (PDF p.16); Proposition 10.10(i), p.23 (PDF p.25): 'a sequential tester adapted to the independent-round transcript filtration, terminating with a decision, whose two errors are at most δ'

import Mathlib
import Definitions.Def_BanditTrajectory

open MeasureTheory

namespace FairReplay

/-- **δ-correct sequential tester** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under
Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…, Theorem 10.4, p.14
(PDF p.16), and Proposition 10.10(i), p.23: "a sequential tester adapted to the independent-round
transcript filtration, terminating with a decision, whose two errors are at most δ").

A tester is a triple `(π, τ, ψ)`: the (possibly randomized, adaptive) action-selection policy `π`,
the stopping time `τ` of the transcript filtration (value `⊤` = never stops), and the decision
`ψ` (`true` = reject the null). `IsDeltaCorrect δ ν₀ ν₁ π τ ψ` says that

1. under the null `ν₀` the tester stops and rejects with probability at most `δ` (type-I error), and
2. under the alternative `ν₁` the tester fails to stop-and-reject with probability at most `δ`
   (type-II error).

**Formalization Note** A run that never stops counts as an error under the alternative, so the
tester that never stops is not δ-correct for `δ < 1`. Under the null, the lower bounds of the
mission assume a finite expected stopping time, which already forces stopping almost surely. -/
def IsDeltaCorrect {k : ℕ} (δ : ℝ) (ν₀ ν₁ : BanditAlgorithm.StochasticBandit k)
    (π : BanditAlgorithm.BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Bool) : Prop :=
  BanditAlgorithm.banditTrajMeasure ν₀ π {ω | τ ω < ⊤ ∧ ψ ω = true} ≤ ENNReal.ofReal δ ∧
    BanditAlgorithm.banditTrajMeasure ν₁ π {ω | ¬ (τ ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ

end FairReplay


