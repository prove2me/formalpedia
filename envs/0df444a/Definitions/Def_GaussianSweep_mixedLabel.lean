-- Prove2me | Definitions.Def_GaussianSweep_mixedLabel
-- name    : GaussianSweep_mixedLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:12.483819+00:00
-- url     : https://prove2.me/theorems/8acc9410-d5d9-493f-80dd-f2a144eaf227
-- title:
--   Mixed labels at radius $R$
-- statement:
--   For a real $R > 0$ and a graph with $\delta(G) \ge 3$, the **mixed labels** are the Gaussian labels of Definition 5.2 with arc lengths $\ell(x \to y) = \tfrac12\ln\big(d(x) - 1\big)$, depending on the tail $x$ only, and $\hat R = R$.
--
--   **Formalization Note** The conditions $R > 0$ and $\delta(G) \ge 3$ are hypotheses of the results, not part of the definition; $d(x) - 1$ is computed in the reals.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2(b), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_GaussianSweep_gaussLabel

namespace GaussianSweep

/-- The mixed labels at radius `R` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2(b), p.28 (PDF p.30)): the arc `x → y`
has length `½ ln(d(x) − 1)`, depending on its tail only, and `R̂ = R`.

**Formalization Note** The paper's conditions (real `R > 0`, `δ(G) ≥ 3`) are hypotheses of the
lemmas that use the labels. `d(x) − 1` is computed in `ℝ`. -/
noncomputable def mixedLabel {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : ℝ) : V → (V → ℝ) → ℝ :=
  gaussLabel G (fun x _ => Real.log ((G.degree x : ℝ) - 1) / 2) R

end GaussianSweep


