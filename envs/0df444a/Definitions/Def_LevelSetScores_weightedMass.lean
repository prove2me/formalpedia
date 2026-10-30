-- Prove2me | Definitions.Def_LevelSetScores_weightedMass
-- name    : LevelSetScores_weightedMass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:26.611976+00:00
-- url     : https://prove2.me/theorems/42e1e218-f825-4460-81eb-454fa9523d4d
-- title:
--   Kernel-weighted mass $\mu_{y,w}(B)$
-- statement:
--   Let $h : \mathbb R^d \to \mathbb R$ be a weight, $w$ a kernel on $\mathbb R^d$, $B \subseteq \mathbb R^d$ and $y \in \mathbb R^d$. The **kernel-weighted mass** of $B$ seen from $y$ is
--   $$\mu_{y,w}(B) = \int_{\mathbb R^d} w(z-y)\,\mathbb 1\{z \in B\}\, h(z)\, dz \in [0,\infty],$$
--   the measure $d\mu_{y,w}(z) = w(z-y)h(z)\,dz$ of the paper evaluated at $B$. With the kernel given as a measure $\nu$ this reads
--   $$\mu_{y,w}(B) = \int \mathbb 1\{y+u \in B\}\, h(y+u)\, d\nu(u).$$
--   For a function kernel $w \ge 0$ (that is, $\nu = w\,dz$) this is the displayed integral; for the Dirac kernel $w = \delta_0$ it is $\mathbb 1\{y \in B\} h(y)$.
--
--   The level set score (11) charges a forecast set its $\lambda$-mass times $\alpha$ minus this quantity.
--
--   **Formalization Note** The paper's kernel $w$ is "a local Borel measure" (Assumption 1(a)), so it is encoded as a measure $\nu$ on `EuclideanSpace ℝ (Fin d)`; $h$ enters as $\max(h,0)$ through `ENNReal.ofReal` (every theorem assumes $h \ge 0$). The value lies in $[0,\infty]$.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, proof of Theorem 2 (i), unnumbered definition of µ_(y,w), p. 33

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace LevelSetScores

/-- **The kernel-weighted mass `μ_{y,w}(B)`.**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, proof of Theorem 2 (i), unnumbered, p. 33: "Let us define two Borel
measures, λ as dλ(z) := h(z)dz, and µy,w as dµy,w(z) := w(z−y)h(z)dz."

`weightedMass h ν B y = ∫⁻ u, 1_B(y + u) h(y + u) dν(u)`, i.e.
`µ_{y,w}(B) = ∫ w(z − y) 1{z ∈ B} h(z) dz` with the kernel `w` given as the measure `ν`.

**Formalization Note.** The paper's kernel `w` is "a local Borel measure" (Assumption 1(a),
p. 32), so it is encoded as a measure `ν` on `ℝᵈ` (`EuclideanSpace ℝ (Fin d)`):
`∫ w(z − y) φ(z) dz` is `∫ φ(y + u) dν(u)`. A function kernel `w ≥ 0` is
`volume.withDensity w` (then this is `∫⁻ z, 1_B(z) h(z) w(z − y) dz` by translation
invariance), the Dirac kernel `δ₀` is `Measure.dirac 0` (then this is `1_B(y) h(y)`). The weight
`h` enters as `ENNReal.ofReal ∘ h`; the theorems assume `h ≥ 0`. The value lies in `ℝ≥0∞` and may
be `∞`. -/
noncomputable def weightedMass {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (B : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ u, B.indicator (fun z => ENNReal.ofReal (h z)) (y + u) ∂ν

end LevelSetScores


