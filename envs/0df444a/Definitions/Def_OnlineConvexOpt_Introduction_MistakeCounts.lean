-- Prove2me | Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts
-- name    : OnlineConvexOpt_Introduction_MistakeCounts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:04:32.935718+00:00
-- url     : https://prove2.me/theorems/b7a79013-e38c-437f-847b-39bd5e2cc805
-- title:
--   Mistake counts for a deterministic algorithm and for an expert
-- statement:
--   Defines the mistake-count quantities used throughout Chapter 1. For a deterministic
--   algorithm's predictions `algPredict : ℕ → Bool` and expert $i$'s predictions
--   `expertPredict : ℕ → Fin N → Bool`, both compared against the true outcome sequence
--   `outcome : ℕ → Bool`, `algMistakes algPredict outcome T` counts the rounds $t < T$ on which
--   `algPredict t ≠ outcome t` — Hazan's $M_T$, p. 9 — and `expertMistakes expertPredict outcome i T`
--   counts the rounds on which expert $i$'s prediction disagreed with the outcome — Hazan's $M_T(i)$.
--
--   $$
--   M_T = |\{\, t < T : \text{algPredict}(t) \neq \text{outcome}(t) \,\}|, \qquad
--   M_T(i) = |\{\, t < T : \text{expertPredict}(t, i) \neq \text{outcome}(t) \,\}|.
--   $$
--
--   These two counts are the objects Theorem 1.1 and Lemmas 1.3–1.4 bound.
--
--   **Formalization Note.** Rounds are indexed from $0$, so `algMistakes _ _ T` counts the book's
--   rounds $1, \dots, T$. Both counts are the cardinality of a `Finset.filter`, hence natural
--   numbers; the milestone theorems cast them to `ℝ` where the book's inequalities mix them with
--   `log N / ε`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 9

import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- Number of mistakes an algorithm's predictions `algPredict` make against the true outcomes
`outcome` on rounds `0, …, T - 1` (Hazan's `M_T`, the book's rounds `1, …, T` shifted down by
one), p. 9. -/
def algMistakes (algPredict outcome : ℕ → Bool) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => algPredict t ≠ outcome t)).card

/-- Number of mistakes expert `i`'s predictions `expertPredict` make against the true outcomes
`outcome` on rounds `0, …, T - 1` (Hazan's `M_T(i)`), p. 9. -/
def expertMistakes (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (i : Fin N)
    (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => expertPredict t i ≠ outcome t)).card

end OnlineConvexOpt.Introduction


