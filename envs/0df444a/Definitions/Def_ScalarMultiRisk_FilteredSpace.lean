-- Prove2me | Definitions.Def_ScalarMultiRisk_FilteredSpace
-- name    : ScalarMultiRisk_FilteredSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:15.111349+00:00
-- url     : https://prove2.me/theorems/a001a946-35aa-410a-9732-bf14dc16ac9a
-- title:
--   Filtered probability space with trivial $\mathcal F_0$ and $\mathcal F=\mathcal F_T$
-- statement:
--   A **filtered probability space** in discrete time is a measurable space $(\Omega,\mathcal F)$ with a probability measure $\mathbb P$ and a filtration $(\mathcal F_t)_{t=0}^T$ such that $\mathcal F_T=\mathcal F$ and $\mathcal F_0$ is trivial, meaning that every $\mathcal F_0$-measurable set has probability $0$ or $1$.
--
--   All objects of the mission live on this space.
--
--   **Formalization Note** The paper's usual conditions are encoded by working modulo $\mathbb P$-a.e. equality: "$\mathcal F_t$-measurable" always means a.e. equal to an $\mathcal F_t$-measurable function.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, §2, p.5

import Mathlib

open MeasureTheory

namespace ScalarMultiRisk

/-- **The filtered probability space of the paper.**
Feinstein, Rudloff, *Scalar multivariate risk measures with a single eligible asset*,
arXiv:1807.10694v5, §2, p.5: "Consider a filtered probability space satisfying the usual
conditions with `F₀` the trivial sigma algebra and `F = F_T`."

**Formalization Note.** Time is discrete, `t ∈ {0, …, T} = Fin (T + 1)`; the paper writes
`(F_t)_{t=0}^T` and every construction sums over `s = t, …, T`. The ambient σ-algebra is `F_T`
(`F_last`). `F₀` is trivial up to `P`-null sets (`F_zero_trivial`). The usual conditions are
encoded by working modulo `P`-a.e. equality: everywhere below "`F_t`-measurable" is
`AEStronglyMeasurable` with respect to `F t`, so the filtration need not contain the null
sets. -/
structure FilteredSpace (Ω : Type*) [m : MeasurableSpace Ω] (T : ℕ) where
  /-- The reference probability measure `ℙ`. -/
  P : Measure Ω
  /-- `ℙ` is a probability measure. -/
  isProb : IsProbabilityMeasure P
  /-- The filtration `(F_t)_{t=0}^T`. -/
  F : Filtration (Fin (T + 1)) m
  /-- `F = F_T`. -/
  F_last : F (Fin.last T) = m
  /-- `F₀` is trivial: every `F₀`-set has probability `0` or `1`. -/
  F_zero_trivial : ∀ A : Set Ω, MeasurableSet[F 0] A → P A = 0 ∨ P A = 1

attribute [instance] FilteredSpace.isProb

end ScalarMultiRisk


