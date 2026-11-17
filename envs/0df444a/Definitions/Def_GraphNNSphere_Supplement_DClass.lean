-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_DClass
-- name    : GraphNNSphere_Supplement_DClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:56.266848+00:00
-- url     : https://prove2.me/theorems/b4c80d9a-f0d8-4cef-a999-e272d512dc32
-- title:
--   Density class $\mathcal D(\mu_+,\mu_-)$ and slack sequences $\vartheta_d$
-- statement:
--   Fix a sequence $\vartheta_d=o(d)$ with $\vartheta_d\ge\log 4$ (an **admissible slack sequence**). For $\mu_+,\mu_-\ge0$, the class $\mathcal D(\mu_+,\mu_-)$ consists of the probability densities on $S^{d-1}$ with
--
--   $$-\mu_-d-\vartheta_d\le\log f\le\mu_+d+\vartheta_d\quad\text{almost everywhere.}$$
--
--   The term $\vartheta_d$ absorbs subexponential factors in the density bounds.
--
--   **Formalization Note** The condition on $\log f$ is written as $e^{-\mu_-d-\vartheta_d}\le f\le e^{\mu_+d+\vartheta_d}$, which is the same condition. The slack sequence is a parameter of the class.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42

import Mathlib
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw

open MeasureTheory Asymptotics Filter

namespace GraphNNSphere

namespace Supplement

/-- An admissible slack sequence: `ϑ_d = o(d)` with `ϑ_d ≥ log 4` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42). -/
def IsSlackSeq (ϑ : ℕ → ℝ) : Prop :=
  ϑ =o[atTop] (fun d : ℕ => (d : ℝ)) ∧ ∀ d, Real.log 4 ≤ ϑ d

/-- The density class `D(μ₊, μ₋)` of the logarithmic regime: probability densities with
`-μ₋ d - ϑ_d ≤ log f ≤ μ₊ d + ϑ_d` almost everywhere (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42).

**Formalization Note** The bound on `log f` is written as `e^{-μ₋ d - ϑ_d} ≤ f ≤ e^{μ₊ d + ϑ_d}`,
which is the same condition (it forces `f > 0`). The slack sequence `ϑ` is a parameter. -/
def DClass (ϑ : ℕ → ℝ) (d : ℕ) (μp μm : ℝ) (f : Sph d → ℝ) : Prop :=
  IsDensity d f ∧ ∀ᵐ x ∂(unif d),
    Real.exp (-(μm * (d : ℝ)) - ϑ d) ≤ f x ∧ f x ≤ Real.exp (μp * (d : ℝ) + ϑ d)

end Supplement

end GraphNNSphere


