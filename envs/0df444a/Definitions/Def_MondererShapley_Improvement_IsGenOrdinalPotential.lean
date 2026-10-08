-- Prove2me | Definitions.Def_MondererShapley_Improvement_IsGenOrdinalPotential
-- name    : MondererShapley_Improvement_IsGenOrdinalPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:55.069698+00:00
-- url     : https://prove2.me/theorems/f8faf673-2dcc-44f1-b955-2375c6048088
-- title:
--   Generalized ordinal potential, equation (2.3)
-- statement:
--   For a finite player set $N$, strategy profiles $Y=\prod_{i\in N}Y^i$, and payoffs $u^i:Y\to\mathbb R$, a **generalized ordinal potential** is a function $P:Y\to\mathbb R$ such that every strict unilateral payoff improvement strictly increases $P$:
--
--   $$
--   u^i(y^{-i},x)-u^i(y^{-i},z)>0\quad\Longrightarrow\quad P(y^{-i},x)-P(y^{-i},z)>0.
--   $$
--
--   Unlike an ordinal potential, $P$ may distinguish profiles between which player $i$ is indifferent. This is the potential characterized by Lemma 2.5.
--
--   **Formalization Note** The common opponents' profile is encoded by `Function.update`; its original $i$-th coordinate is ignored.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 129 (PDF p. 6), equation (2.3)

import Mathlib

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Equation (2.3): a strict payoff gain implies a strict potential gain. -/
def IsGenOrdinalPotential (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ) : Prop :=
  ∀ (i : ι) (y : ∀ i, Y i) (x z : Y i),
    0 < u i (Function.update y i x) - u i (Function.update y i z) →
      0 < P (Function.update y i x) - P (Function.update y i z)

end MondererShapley.Improvement


