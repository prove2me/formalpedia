-- Prove2me | Definitions.Def_OnlineLearningOCO_Winnow_uegWeights
-- name    : OnlineLearningOCO_Winnow_uegWeights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:27.487737+00:00
-- url     : https://prove2.me/theorems/032d6edb-f971-4cc4-a746-d85c64ff55db
-- title:
--   Unnormalized Exponentiated Gradient weights $w_t[i]=\lambda e^{-\eta z_{1:t-1}[i]}$ (§2.8, p. 154)
-- statement:
--   The **unnormalized Exponentiated Gradient** algorithm (unnormalized-EG) has parameters $\eta,\lambda>0$. It starts from $w_1=(\lambda,\dots,\lambda)\in\mathbb R^d$ and, after observing the linear loss vector $z_t\in\mathbb R^d$, updates every coordinate multiplicatively,
--   $$w_{t+1}[i]=w_t[i]\,e^{-\eta z_t[i]},\qquad i=1,\dots,d .$$
--   Unrolled, $w_t[i]=\lambda\,e^{-\eta z_{1:t-1}[i]}$ with $z_{1:t-1}=\sum_{s<t}z_s$. Unlike normalized EG, the weights are not projected back onto the probability simplex.
--
--   Winnow is unnormalized-EG with $\lambda=1/d$ run on a particular surrogate loss.
--
--   **Formalization Note** Rounds are numbered from $0$: `uegWeights η lam z t i` $=\lambda\exp(-\eta\sum_{s<t}z_s[i])$, so $t=0$ is the paper's $w_1$. The parameter is named `lam` because `λ` is reserved in Lean. Positivity of $\eta,\lambda$ is a hypothesis of the theorems, not part of the definition.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 154, Unnormalized Exponentiated Gradient (unnormalized-EG) box

import Mathlib

namespace OnlineLearningOCO.Winnow

open Finset

/-- The weights of the unnormalized Exponentiated Gradient algorithm (§2.8, p. 154):
parameters `η, λ > 0`, `w₁ = (λ, …, λ)`, `w_{t+1}[i] = w_t[i] e^{-η z_t[i]}`; unrolled,
`w_t[i] = λ e^{-η z_{1:t-1}[i]}`. Rounds are numbered from `0`:
`uegWeights η lam z t i = lam * exp (-η * ∑_{s<t} z s i)`, so `t = 0` is the paper's `w₁`.
(`lam` stands for the paper's `λ`, a reserved word in Lean.) -/
noncomputable def uegWeights {d : ℕ} (η lam : ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) (i : Fin d) : ℝ :=
  lam * Real.exp (-η * ∑ s ∈ range t, z s i)

end OnlineLearningOCO.Winnow


