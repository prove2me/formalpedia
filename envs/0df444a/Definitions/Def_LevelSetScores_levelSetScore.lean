-- Prove2me | Definitions.Def_LevelSetScores_levelSetScore
-- name    : LevelSetScores_levelSetScore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:55.152651+00:00
-- url     : https://prove2.me/theorems/33a650c1-ca70-49d7-9f84-148018056467
-- title:
--   The level set score $(S')^\Gamma(A,y;w,h,\alpha)$ of (11)
-- statement:
--   Let $h \ge 0$ be integrable with $d\lambda = h\,dz$, let $w$ be a kernel, $\alpha \in \mathbb R$, $A \subseteq \mathbb R^d$ a forecast set and $y \in \mathbb R^d$ a realization. The **level set score** (11) is
--   $$(S')^\Gamma(A, y; w, h, \alpha) = \int_{\mathbb R^d} \big(\alpha - w(z-y)\big)\,\mathbb 1\{z \in A\}\, h(z)\, dz = \alpha\,\lambda(A) - \mu_{y,w}(A),$$
--   where $\mu_{y,w}$ is the kernel-weighted mass.
--
--   With $w = \delta_0$ it is the excess mass score $\alpha\lambda(A) - \mathbb 1\{y\in A\}h(y)$ of (12); with the Heaviside kernel it is the CDF level set score (13).
--
--   **Formalization Note** The score is defined as $\alpha\int_A h - \mu_{y,w}(A)$, the split the paper uses in its proof; it is a real number, and `ENNReal.toReal` returns $0$ when $\mu_{y,w}(A) = \infty$ (where the paper's score is $-\infty$). Every theorem that uses the score assumes $\mu_{y,w}(A) < \infty$ for $P$-almost every $y$.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, Theorem 2, display (11), p. 13

import Mathlib
import Definitions.Def_LevelSetScores_weightedMass

open MeasureTheory
open scoped ENNReal

namespace LevelSetScores

/-- **The level set scoring function (11).**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, Theorem 2, display (11), p. 13:
"(S′)Γ(A,y;w,h,α) = ∫Rd (α − w(z − y)) 1{z ∈ A} h(z) dz."

`levelSetScore h ν α A y = α · λ(A) − µ_{y,w}(A)`, where `λ(A) = ∫_A h(z) dz` and
`µ_{y,w}(A) = weightedMass h ν A y`.

**Formalization Note.** The paper's integral `∫ (α − w(z − y)) 1{z ∈ A} h(z) dz` is split into
`α ∫_A h` (finite, since `h` is integrable) minus `µ_{y,w}(A)`; this is the form the paper itself
uses in the proof (`∆′′`, p. 33). The kernel `w` is the measure `ν` (see `weightedMass`).
`µ_{y,w}(A) ∈ ℝ≥0∞` is converted with `ENNReal.toReal`, which returns `0` when the mass is `∞`
(where the paper's score is `−∞`); every theorem using this score assumes the mass finite
`P`-almost everywhere, so this junk value is never seen under the expectation. -/
noncomputable def levelSetScore {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (α : ℝ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  α * (∫ z in A, h z) - (weightedMass h ν A y).toReal

end LevelSetScores


