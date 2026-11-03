-- Prove2me | Definitions.Def_SparseBatchBandit_ModelC
-- name    : SparseBatchBandit_ModelC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:02.856741+00:00
-- url     : https://prove2.me/theorems/4501f1cf-8813-4ca3-8fb0-831aec6abfc8
-- title:
--   Model-C with iid contexts and noises
-- statement:
--   **Model-C.** At each round $t$ the learner sees $K$ contexts $x_{t,a}\in\mathbb R^d$; arm $a$ gives reward $x_{t,a}^\top\theta^\star+\xi_t$. On a probability space:
--
--   1. the $Kd$-dimensional vectors $(x_{t,a})_{a\in[K]}$ are iid across $t$, with arbitrary correlation across arms;
--   2. the noises $\xi_t$ are iid and 1-sub-Gaussian, $\mathbb E[e^{\lambda\xi_t}]\le e^{\lambda^2/2}$ for every $\lambda\in\mathbb R$;
--   3. the family of contexts is independent of the family of noises.
--
--   **Formalization Note** Mathlib's `HasSubgaussianMGF` includes integrability and implies mean zero, so "zero-mean" is contained in it. Item 3 is not stated in the paper; its proof uses it on p.28.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §2.1–2.2, p.5

import Mathlib
open MeasureTheory ProbabilityTheory

namespace SparseBatchBandit

/-- **Model-C** with the distributional assumptions of §2.2, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.5 (PDF 5). `x ω t a` is the
context `x_{t,a}`, `ξ ω t` the noise `ξ_t`:
the `Kd`-dimensional vectors `(x_{t,a})_a` are iid across `t`, with no restriction across `a`; the
noises are iid and 1-sub-Gaussian, `E[e^{λξ_t}] ≤ e^{λ²/2}` for all `λ`; and the contexts are
independent of the noises.

**Formalization Note.** `HasSubgaussianMGF` contains the integrability of `e^{λξ_t}`, and it implies
`E[ξ_t] = 0`, so the mean is not a separate field. The page does not state the independence of
contexts and noises; its proof uses it on p.28. -/
structure ModelC {Ω : Type*} [MeasurableSpace Ω] {T K d : ℕ} (P : Measure Ω)
    (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) : Prop where
  /-- the contexts are random variables -/
  meas_x : Measurable x
  /-- the noises are random variables -/
  meas_ξ : Measurable ξ
  /-- the context vectors of different rounds are independent -/
  indep_x : iIndepFun (fun t ω => x ω t) P
  /-- the context vectors of different rounds have the same law -/
  ident_x : ∀ t t', IdentDistrib (fun ω => x ω t) (fun ω => x ω t') P P
  /-- the noises are independent -/
  indep_ξ : iIndepFun (fun t ω => ξ ω t) P
  /-- the noises have the same law -/
  ident_ξ : ∀ t t', IdentDistrib (fun ω => ξ ω t) (fun ω => ξ ω t') P P
  /-- the noises are 1-sub-Gaussian -/
  subgaussian_ξ : ∀ t, HasSubgaussianMGF (fun ω => ξ ω t) 1 P
  /-- the contexts are independent of the noises -/
  indep_x_ξ : IndepFun x ξ P

end SparseBatchBandit


