-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral
-- name    : WassersteinLinOpt_Ball_quasiIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:26:00.851+00:00
-- url     : https://prove2.me/theorems/0c6edb43-186d-40e3-904a-614a79978a9a
-- title:
--   Extended-real integral $\int g\,d\gamma=\int[g]_+\,d\gamma-\int[-g]_+\,d\gamma$
-- statement:
--   For a measurable space $\alpha$, a measure $\gamma$ on it and a function $g:\alpha\to\mathbb R$, the paper's integral of $g$ (used in problems (3), (10) and (11)) is
--
--   $$\int g\,d\gamma=\int [g]_+\,d\gamma-\int[-g]_+\,d\gamma\in[-\infty,+\infty],$$
--
--   where $[t]_+=\max\{t,0\}$. It is meaningful whenever at least one of the two integrals on the right is finite, which the paper assumes wherever it is used.
--
--   **Formalization Note.** Both parts are lower Lebesgue integrals in `ℝ≥0∞`, cast to `EReal` and subtracted. In `EReal`, `⊤ - ⊤ = ⊥`; every theorem that uses this integral therefore carries the paper's hypothesis that one of the two parts is finite, so that case never arises. The Bochner integral is deliberately not used, because it returns `0` for non-integrable functions.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1108 (problem (3) and the assumption below it) and p. 1121 (Proposition 1)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- The extended-real integral used throughout the paper (p. 1108 and p. 1121):
`∫ g dγ := ∫ [g]₊ dγ − ∫ [−g]₊ dγ ∈ [−∞, +∞]`. It is the paper's integral whenever at least
one of the two parts is finite; every statement using it carries that hypothesis, because
`EReal` evaluates `⊤ − ⊤` to `⊥`. -/
noncomputable def quasiIntegral {α : Type*} [MeasurableSpace α] (g : α → ℝ) (γ : Measure α) :
    EReal :=
  ((∫⁻ z, ENNReal.ofReal (g z) ∂γ : ℝ≥0∞) : EReal) - ((∫⁻ z, ENNReal.ofReal (-g z) ∂γ : ℝ≥0∞) : EReal)

end WassersteinLinOpt.Ball


