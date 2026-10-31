-- Prove2me | Definitions.Def_FoundationsRL_OnlineLearning_ExcessRisk
-- name    : FoundationsRL_OnlineLearning_ExcessRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:50.431263+00:00
-- url     : https://prove2.me/theorems/6bf7e769-f84c-4ebf-81ed-fcb1434de7c8
-- title:
--   Expected loss (1.3), excess loss (1.7) and the online-to-batch average
-- statement:
--   Let $M^\star$ be a distribution on $\mathcal X\times\mathcal Y$ and $\mathcal F$ a class of functions.
--
--   1. **Expected loss.** $L(f)=\mathbb E_{(x,y)\sim M^\star}[\ell(f(x),y)]$.
--   2. **Excess loss.**
--   $$
--   \mathcal E(f)=L(f)-\min_{f'\in\mathcal F}L(f').
--   $$
--   3. **Online-to-batch average.** $\hat f(x)=\frac1T\sum_{t=1}^T\hat f^t(x)$, for predictions in a real vector space.
--
--   These are the statistical-learning quantities through which Proposition 2 reads regret as a bound on excess risk.
--
--   **Formalization Note** The minimum is the real infimum over $\mathcal F$; statements using it carry the hypotheses that keep $L$ integrable on $\mathcal F$ and bounded below there.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.3), p. 7, (1.7), p. 8, Proposition 2, p. 14

import Mathlib

open MeasureTheory

namespace FoundationsRL.OnlineLearning

/-- **Expected loss** `L(f) = E_{(x,y) ∼ M⋆} ℓ(f(x), y)`, (1.3), p. 7, arXiv:2312.16730v1, written as a
Bochner integral against the law `M` of an example. -/
noncomputable def expectedLoss {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ℓ : Y' → Y → ℝ) (M : Measure (X × Y)) (f : X → Y') : ℝ :=
  ∫ z, ℓ (f z.1) z.2 ∂M

/-- **Excess loss** `E(f) = L(f) - min_{f' ∈ F} L(f')`, (1.7), p. 8, arXiv:2312.16730v1.

**Formalization Note.** The minimum is the real infimum over `F`. Statements that use this definition
carry the hypotheses that keep `L` integrable on `F` and bounded below there. -/
noncomputable def excessRisk {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ℓ : Y' → Y → ℝ) (M : Measure (X × Y)) (F : Set (X → Y')) (f : X → Y') : ℝ :=
  expectedLoss ℓ M f - ⨅ g : F, expectedLoss ℓ M g

/-- **Online-to-batch average** `f̂(x) = (1/T) ∑_{t=1}^T f̂^t(x)`, Proposition 2, p. 14,
arXiv:2312.16730v1, for predictions in a real vector space. -/
noncomputable def onlineAverage {X V : Type*} [AddCommMonoid V] [Module ℝ V] (T : ℕ)
    (fhat : ℕ → X → V) : X → V :=
  fun x => ((1 : ℝ) / T) • ∑ t ∈ Finset.range T, fhat t x

end FoundationsRL.OnlineLearning


