-- Prove2me | Definitions.Def_HighConfRobust_IsHighConfidence
-- name    : HighConfRobust_IsHighConfidence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:29.944569+00:00
-- url     : https://prove2.me/theorems/ebbe666b-b61e-411b-8671-642272ba6279
-- title:
--   $(\alpha,\beta,\mathcal F)$-high-confidence algorithm
-- statement:
--   Fix a statistical task with sample space $\mathcal X$, output space $\mathcal Y$, parameter map $\theta$ and loss $\mathrm{loss}:\mathcal Y\times\mathcal Y\to\mathbb R_{\ge0}$. A randomized algorithm $A:\mathcal X^n\to\mathcal Y$ with random seed $\omega\sim\nu$ is **$(\alpha,\beta,\mathcal F)$-high-confidence over $n$ samples** if for every distribution $D\in\mathcal F$,
--
--   $$
--   \Pr_{S\sim D^{\otimes n},\ \omega\sim\nu}\big[\mathrm{loss}(A(S,\omega),\theta(D))>\alpha\big]\le\beta .
--   $$
--
--   That is, with probability at least $1-\beta$ over the samples and the internal randomness, the output is within loss $\alpha$ of the true parameter. This is the basic accuracy guarantee from which the mission builds robust algorithms.
--
--   **Formalization Note** Distributions are probability measures on $\mathcal X$ and $\theta$ is defined on all of them (only its values on $\mathcal F$ matter). A randomized algorithm is a map $(\mathcal X^n)\times\Omega\to\mathcal Y$ together with a probability measure $\nu$ on the seed space $\Omega$; the joint law is $D^{\otimes n}\otimes\nu$. The guarantee bounds the measure of the failure set by $\beta$, which is the same as "success with probability at least $1-\beta$" whenever that set is measurable.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Definition 1.3, p.5

import Mathlib

namespace HighConfRobust

open MeasureTheory

/-- A randomized algorithm `A` on `n` samples with seed law `ν` is
**`(α, β, F)`-high-confidence** (Definition 1.3, p.5) for the task with loss `loss` and parameter map
`θ`: for every distribution `D ∈ F`, with probability at least `1 − β` over `S ∼ D^{⊗n}` and the
seed `ω ∼ ν`, `loss (A S ω) (θ D) ≤ α`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153),
Definition 1.3, p.5.

**Formalization Note** Distributions are `ProbabilityMeasure X`; `θ` is defined on all of them (only
its values on the family matter). A randomized algorithm is a map `A : (Fin n → X) → Ω → Y` together
with a probability measure `ν` on the seed space `Ω`; the joint law of samples and seed is
`(Measure.pi fun _ => D).prod ν`. The guarantee is stated on the **failure set**
`{(S, ω) | α < loss (A S ω) (θ D)}`: its measure is at most `β`. For a measurable failure set this is
exactly "success with probability at least `1 − β`"; for a non-measurable one the measure is the
outer measure. -/
def IsHighConfidence {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (loss : Y → Y → ℝ) (θ : ProbabilityMeasure X → Y) {n : ℕ}
    (A : (Fin n → X) → Ω → Y) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (α β : ℝ) (F : Set (ProbabilityMeasure X)) : Prop :=
  ∀ D ∈ F, ((Measure.pi fun _ : Fin n => (D : Measure X)).prod ν)
    {p | α < loss (A p.1 p.2) (θ D)} ≤ ENNReal.ofReal β

end HighConfRobust


