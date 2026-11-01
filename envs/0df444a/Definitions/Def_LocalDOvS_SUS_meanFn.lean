-- Prove2me | Definitions.Def_LocalDOvS_SUS_meanFn
-- name    : LocalDOvS_SUS_meanFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:19.669751+00:00
-- url     : https://prove2.me/theorems/0082565e-296c-4a1d-bf34-68039c574e43
-- title:
--   Objective $f(x)=\mathbb E[F(x,\xi_x)]$
-- statement:
--   The **objective** of a model is the mean output
--
--   $$
--   f(x)=\mathbb E[F(x,\xi_x)]=\int y\,\nu_x(dy).
--   $$
--
--   Problem (1) of the paper is to find $\min_{x\in X}f(x)$ when $f$ can only be estimated by simulation.
--
--   **Formalization Note** This is a Bochner integral; for the sub-Gaussian models of $\mathcal M_C$ the outputs are integrable, so the value is the true mean.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §2, p.8

import Mathlib
import Definitions.Def_LocalDOvS_SUS_Model

open MeasureTheory

namespace LocalDOvS.SUS

/-- The objective `f(x) := E[F(x, ξ_x)]` of a model (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §2,
p.8): the mean of the output law at `x`.

**Formalization Note.** This is a Bochner integral, so it is `0` for a non-integrable law; the
models of `InMC` have sub-Gaussian (hence integrable) outputs at every `x ∈ [N]`, so the junk
value never occurs there. -/
noncomputable def meanFn (M : Model) (x : ℕ) : ℝ :=
  ∫ y, y ∂(M.law x)

end LocalDOvS.SUS


