-- Prove2me | Definitions.Def_LocalDOvS_SUS_simCost
-- name    : LocalDOvS_SUS_simCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:30:28.415992+00:00
-- url     : https://prove2.me/theorems/fe681010-f1bc-46cd-bc2d-8f8741c903c1
-- title:
--   Expected simulation cost $T(\epsilon,\delta,\mathcal M_C)$
-- statement:
--   The **expected simulation cost** of $(\epsilon,\delta)$-PGS over the class $\mathcal M_C$ on $[N]$ is
--
--   $$
--   T(\epsilon,\delta,\mathcal M_C)=\inf_{A}\ \sup_{M\in\mathcal M_C}\ \mathbb E_M[\tau_A],
--   $$
--
--   the infimum running over the measurable sequential algorithms on $[N]$ that are $(\epsilon,\delta)$-PGS on every model of $\mathcal M_C$. It measures the least worst-case number of simulations needed to guarantee a good selection.
--
--   **Formalization Note** Valued in $[0,\infty]$, with $\mathbb E[\tau_A]$ the lower Lebesgue integral of $\tau_A$. An empty infimum is $\infty$, so a finite upper bound asserts that a PGS algorithm exists. The class is that of deterministic sequential rules, contained in the paper's class of algorithms, so an upper bound on this $T$ bounds the paper's.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Definition 2, p.10

import Mathlib
import Definitions.Def_LocalDOvS_SUS_IsPGS
import Definitions.Def_LocalDOvS_SUS_IsMeasurableAlg
import Definitions.Def_LocalDOvS_SUS_IsValidAlg
import Definitions.Def_LocalDOvS_SUS_InMC

open MeasureTheory
open scoped NNReal ENNReal

namespace LocalDOvS.SUS

/-- The expected simulation cost `T(ε, δ, M_C)` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2,
Definition 2, p.10: `T(O, M) := inf_{A is (O, M)} sup_{M ∈ M} E[τ_A]`, with
`T(ε, δ, M_C) := T((ε, δ)-PGS, M_C)`), for `X = [N]` and sub-Gaussian parameter bound `σ²`.
The infimum runs over the measurable sequential algorithms on `[N]` that are `(ε, δ)`-PGS on
every model of `M_C` (Definition 1, p.9); the supremum over the models of `M_C`.

**Formalization Note.** Valued in `ℝ≥0∞`: `E[τ_A]` is the lower Lebesgue integral of
`τ_A ∈ ℕ∞`, and an empty infimum is `⊤`, so a finite upper bound on `simCost` asserts that some
`(ε, δ)`-PGS algorithm exists. The class is that of deterministic sequential rules; it is
contained in the paper's class of algorithms, so an upper bound here is an upper bound on the
paper's `T`. -/
noncomputable def simCost (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ) : ℝ≥0∞ :=
  ⨅ (A : SeqAlg) (_ : IsMeasurableAlg A ∧ IsValidAlg N A ∧
      ∀ M : Model, InMC N σ M → IsPGS N ε δ A M),
    ⨆ (M : Model) (_ : InMC N σ M), ∫⁻ ω, ((stopTime A ω : ℕ∞) : ℝ≥0∞) ∂(tapeMeasure M)

end LocalDOvS.SUS


