-- Prove2me | Definitions.Def_HighConfRobust_extFamily
-- name    : HighConfRobust_extFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:39.269333+00:00
-- url     : https://prove2.me/theorems/b0eee57b-a522-4de9-af2a-660e4be9c315
-- title:
--   Enlarged family $\mathcal F_{\mathrm{ext}}$ of Assumption 4.1
-- statement:
--   Let $\mathcal F$ be a family of distributions on $\mathcal X$, $f:\mathcal X\to\mathcal X$ a measurable pre-processing map and $a>0$. The **enlarged family** is
--
--   $$
--   \mathcal F_{\mathrm{ext}}=\big\{\,f(D')\ :\ D\in\mathcal F,\ \mathrm{TV}(D,D')\le a\,\big\},
--   $$
--
--   where $f(D')$ is the distribution of $f(Z)$ for $Z\sim D'$. It is the set of pre-processed laws of all distributions within total variation $a$ of the family; Assumption 4.1 asks the parameter map to be Lipschitz on it.
--
--   **Formalization Note** $f(D')$ is the pushforward probability measure, which requires $f$ to be measurable; $D'$ ranges over all probability measures on $\mathcal X$.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Assumption 4.1, p.17 (first bullet)

import Mathlib
import Definitions.Def_TotalVariationDist

namespace HighConfRobust

open MeasureTheory

/-- The **enlarged family** `F_ext` of Assumption 4.1 (p.17): all distributions of the form `f(D')`
(the law of `f(Z)` for `Z ∼ D'`) where `D ∈ F` and `TV(D, D') ≤ a`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153),
Assumption 4.1, p.17 (first bullet).

**Formalization Note** `f(D')` is the pushforward `D'.map f` as a probability measure, which needs
`f` measurable (the proof `hf` is an argument). `D'` ranges over all probability measures on `X`;
TV is the public `MarkovChainCLT.tvDist`. -/
def extFamily {X : Type*} [MeasurableSpace X] (f : X → X) (hf : Measurable f) (a : ℝ)
    (F : Set (ProbabilityMeasure X)) : Set (ProbabilityMeasure X) :=
  {E | ∃ D ∈ F, ∃ D' : ProbabilityMeasure X,
    MarkovChainCLT.tvDist (D : Measure X) (D' : Measure X) ≤ a ∧ E = D'.map hf.aemeasurable}

end HighConfRobust


