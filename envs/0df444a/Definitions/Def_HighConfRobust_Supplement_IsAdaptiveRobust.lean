-- Prove2me | Definitions.Def_HighConfRobust_Supplement_IsAdaptiveRobust
-- name    : HighConfRobust_Supplement_IsAdaptiveRobust
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:42:59.175434+00:00
-- url     : https://prove2.me/theorems/9ca61cb8-2cc1-4fac-9773-1879115342c9
-- title:
--   $(\varepsilon,\alpha,\beta,\mathcal F)$-robust algorithm (adaptive contamination)
-- statement:
--   Fix a statistical task with sample space $\mathcal X$, output space $\mathcal Y$, parameter map $\theta$ and loss $\mathrm{loss}$. A randomized algorithm $A:\mathcal X^m\times\Omega\to\mathcal Y$ with seed law $\nu$ is **$(\varepsilon,\alpha,\beta,\mathcal F)$-robust over $m$ samples** if for every distribution $D\in\mathcal F$ and every adaptive $\varepsilon$-adversary $T$ with seed law $\mu$,
--
--   $$
--   \Pr_{S\sim D^{\otimes m},\ \omega_T\sim\mu,\ \omega\sim\nu}\big[\mathrm{loss}(A(T(S,\omega_T),\omega),\theta(D))>\alpha\big]\le\beta .
--   $$
--
--   The adversary sees the clean sample before corrupting it and may depend on $D$; the error is measured against the parameter of the clean distribution. This is the strongest of the paper's contamination models and the conclusion of its reduction from adaptive robustness.
--
--   **Formalization Note** The adversary is a randomized algorithm and, like every algorithm of the mission, is jointly measurable in the dataset and its seed; its seed space ranges over all measurable spaces in the universe of $\mathcal X$. The guarantee bounds the measure of the failure set under $D^{\otimes m}\otimes\mu\otimes\nu$, as in the published high-confidence definition.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Definition 1.5, p.5

import Mathlib
import Definitions.Def_HighConfRobust_Supplement_IsAdaptiveAdversary

namespace HighConfRobust.Supplement

universe u

open MeasureTheory

/-- A randomized algorithm `A` on `m` samples with seed law `ν` is **`(ε, α, β, F)`-robust**
against adaptive adversaries (Definition 1.5, p.5): for every `D ∈ F` and every adaptive
`ε`-adversary `T` (a randomized algorithm with its own seed law `μ`), with probability at least
`1 − β` over `S ∼ D^{⊗m}`, the adversary's seed and the seed of `A`,
`loss (A (T S ωt) ω) (θ D) ≤ α`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Definition 1.5, p.5.

**Formalization Note** Conventions as in the published `HighConfRobust.IsHighConfidence`:
distributions are `ProbabilityMeasure X`, the joint law is `D^{⊗m} ⊗ (μ ⊗ ν)`, and the guarantee
bounds the measure of the failure set `{α < loss (A (T S ωt) ω) (θ D)}` by `β`. The adversary may
depend on `D` (it is quantified after `D`); it is a randomized algorithm, so, as for every algorithm
of the mission, it is jointly measurable in the dataset and its seed. Its seed space ranges over
every measurable space in the universe of `X`. -/
def IsAdaptiveRobust {X : Type u} {Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (loss : Y → Y → ℝ) (θ : ProbabilityMeasure X → Y) {m : ℕ}
    (A : (Fin m → X) → Ω → Y) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ε α β : ℝ) (F : Set (ProbabilityMeasure X)) : Prop :=
  ∀ D ∈ F, ∀ (Ωt : Type u) [MeasurableSpace Ωt] (μ : Measure Ωt) [IsProbabilityMeasure μ]
    (T : (Fin m → X) → Ωt → (Fin m → X)),
    Measurable (Function.uncurry T) → IsAdaptiveAdversary ε T →
      ((Measure.pi fun _ : Fin m => (D : Measure X)).prod (μ.prod ν))
        {p | α < loss (A (T p.1 p.2.1) p.2.2) (θ D)} ≤ ENNReal.ofReal β

end HighConfRobust.Supplement


