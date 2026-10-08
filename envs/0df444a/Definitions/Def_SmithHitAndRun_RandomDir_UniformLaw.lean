-- Prove2me | Definitions.Def_SmithHitAndRun_RandomDir_UniformLaw
-- name    : SmithHitAndRun_RandomDir_UniformLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:39.404118+00:00
-- url     : https://prove2.me/theorems/5e53c1ef-bd19-4010-8202-da5cd70b15e6
-- title:
--   Uniform distribution $\lambda(A)=V(A)/V(S)$ over a region $S$
-- statement:
--   For a region $S\subseteq\mathbb R^n$ with $n$-dimensional content (Lebesgue measure) $V(S)$, the **uniform distribution over $S$** is
--   $$\lambda(A)=\frac{V(A\cap S)}{V(S)}$$
--   for measurable $A\subseteq\mathbb R^n$. When $0<V(S)<\infty$, for instance when $S$ is open, bounded and nonempty, it is a probability measure carried by $S$.
--
--   It is the target distribution of every mixing algorithm in the paper, and the stationary law of Lemma 1.
--
--   **Formalization Note** Defined as `(volume S)⁻¹ • volume.restrict S` on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1300, Lemma 1

import Mathlib

namespace SmithHitAndRun.RandomDir

open MeasureTheory

/-- The uniform distribution `λ` over a region `S ⊆ ℝⁿ` (Smith 1984, p. 1300, Lemma 1):
`λ(A) = V(A ∩ S) / V(S)`, Lebesgue measure restricted to `S` and normalized by the
`n`-dimensional content `V(S)` of `S`. It is a probability measure when `0 < V(S) < ∞`. -/
noncomputable def unif {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume S)⁻¹ • volume.restrict S

end SmithHitAndRun.RandomDir


