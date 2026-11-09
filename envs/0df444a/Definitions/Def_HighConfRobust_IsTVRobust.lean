-- Prove2me | Definitions.Def_HighConfRobust_IsTVRobust
-- name    : HighConfRobust_IsTVRobust
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:35.511881+00:00
-- url     : https://prove2.me/theorems/d088427e-f830-4fad-8e90-932b078dfd16
-- title:
--   $(\varepsilon,\alpha,\beta,\mathcal F)$-TV-robust (oblivious-robust) algorithm
-- statement:
--   In the setting of the high-confidence definition, a randomized algorithm $A:\mathcal X^n\to\mathcal Y$ with seed $\omega\sim\nu$ is **$(\varepsilon,\alpha,\beta,\mathcal F)$-TV-robust over $n$ samples** (oblivious-robust) if for every $D\in\mathcal F$ and every distribution $D'$ with $\mathrm{TV}(D,D')\le\varepsilon$,
--
--   $$
--   \Pr_{S\sim D'^{\otimes n},\ \omega\sim\nu}\big[\mathrm{loss}(A(S,\omega),\theta(D))>\alpha\big]\le\beta .
--   $$
--
--   The samples are drawn from the contaminated distribution $D'$, while the error is measured against the parameter $\theta(D)$ of the clean distribution $D$. This models an oblivious adversary that perturbs the sampling distribution by at most $\varepsilon$ in total variation.
--
--   **Formalization Note** Total variation is the public `MarkovChainCLT.tvDist`, $\sup_A|D(A)-D'(A)|$ over measurable $A$. The other conventions are those of the high-confidence definition.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Definition 1.4, p.5

import Mathlib
import Definitions.Def_TotalVariationDist

namespace HighConfRobust

open MeasureTheory

/-- A randomized algorithm `A` on `n` samples with seed law `ν` is **`(ε, α, β, F)`-TV-robust**
(oblivious-robust, Definition 1.4, p.5): for every `D ∈ F` and every distribution `D'` with
`TV(D, D') ≤ ε`, with probability at least `1 − β` over `S ∼ D'^{⊗n}` and the seed `ω ∼ ν`,
`loss (A S ω) (θ D) ≤ α`. The samples come from the contaminated `D'`; the error is measured against
the parameter `θ D` of the clean distribution.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153),
Definition 1.4, p.5.

**Formalization Note** TV is the public `MarkovChainCLT.tvDist` (`sup_A |D(A) − D'(A)|` over measurable
`A`). Conventions as in `IsHighConfidence`: distributions are `ProbabilityMeasure X`, the joint law
is `(Measure.pi fun _ => D').prod ν`, and the guarantee bounds the measure of the failure set
`{(S, ω) | α < loss (A S ω) (θ D)}` by `β`. -/
def IsTVRobust {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (loss : Y → Y → ℝ) (θ : ProbabilityMeasure X → Y) {n : ℕ}
    (A : (Fin n → X) → Ω → Y) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ε α β : ℝ) (F : Set (ProbabilityMeasure X)) : Prop :=
  ∀ D ∈ F, ∀ D' : ProbabilityMeasure X,
    MarkovChainCLT.tvDist (D : Measure X) (D' : Measure X) ≤ ε →
      ((Measure.pi fun _ : Fin n => (D' : Measure X)).prod ν)
        {p | α < loss (A p.1 p.2) (θ D)} ≤ ENNReal.ofReal β

end HighConfRobust


