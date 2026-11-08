-- Prove2me | Definitions.Def_GaussianSweep_paddedLabel
-- name    : GaussianSweep_paddedLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:56.255899+00:00
-- url     : https://prove2.me/theorems/f63846b7-6d0d-4111-a8cf-823a489d45d8
-- title:
--   Padded labels of degree $p$ at radius $R$
-- statement:
--   For integers $p \ge 3$ and $R \ge 1$, the **padded labels of degree $p$** are the Gaussian labels of Definition 5.2 in which every arc has length $\tfrac12\ln(p-1)$ and $\hat R = \tfrac R2 \ln(p-1)$. Then $D(v,w) = \tfrac12\ln(p-1)\,\mathrm{dist}(v,w)$, $B(v) = B_R(v)$ and
--   $$
--   X_v = \sum_{w \in B_R(v)} (p-1)^{-\mathrm{dist}(v,w)/2} Z_w .
--   $$
--   For $p = 3$ these are the geometric labels with coefficients $2^{-\mathrm{dist}(v,w)/2}$, used for graphs of maximum degree $3$.
--
--   **Formalization Note** The paper's conditions ($p \ge 3$, $R \ge 1$, $\Delta(G) \le p$) are hypotheses of the results, not part of the definition.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2(a), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_GaussianSweep_gaussLabel

namespace GaussianSweep

/-- The padded labels of degree `p` at radius `R` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2(a), p.28 (PDF p.30)):
every arc has length `½ ln(p − 1)` and `R̂ = (R/2) ln(p − 1)`. For `p = 3` these are the geometric
labels used in Theorem 8.1.

**Formalization Note** The paper's conditions (integers `p ≥ 3`, `R ≥ 1`, `Δ(G) ≤ p`) are
hypotheses of the lemmas that use the labels, not part of the definition. -/
noncomputable def paddedLabel {V : Type*} [Fintype V] (G : SimpleGraph V) (p R : ℕ) :
    V → (V → ℝ) → ℝ :=
  gaussLabel G (fun _ _ => Real.log ((p : ℝ) - 1) / 2) ((R : ℝ) / 2 * Real.log ((p : ℝ) - 1))

end GaussianSweep


