-- Prove2me | Definitions.Def_SongZhangKLS_IsRegular
-- name    : SongZhangKLS_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:59.193126+00:00
-- url     : https://prove2.me/theorems/bc082b39-0e1e-4266-9d91-f1f762587d93
-- title:
--   Regular measures: $d\mu=e^{-W}dx$ with $W\in C^\infty$, $aI\preceq D^2W$, $\nabla W$ globally $b$-Lipschitz
-- statement:
--   Let $\mu$ be a measure on $\mathbb R^n$ and $W:\mathbb R^n\to\mathbb R$. The function $W$ is a **regular potential** of $\mu$ if
--
--   1. $d\mu=e^{-W}\,dx$, with $dx$ Lebesgue measure;
--   2. $W\in C^\infty(\mathbb R^n)$;
--   3. for some $0<a\le b<\infty$, $\mu$ is $a$-strongly log-concave, that is $W(x)-a\|x\|^2/2$ is convex, and $b$-smooth, that is $\nabla W$ is globally $b$-Lipschitz.
--
--   The measure $\mu$ is **regular** if it has a regular potential. The constants $a,b$ may depend on $\mu$.
--
--   Regular measures are the class on which the paper's curvature comparison (Theorem 5.1) is proved; Lemma 3.2 reduces general isotropic log-concave measures to them.
--
--   **Formalization Note** The density is $x\mapsto e^{-W(x)}$ as an extended nonnegative real, $\nabla W$ is Mathlib's `gradient`, and convexity is `ConvexOn ℝ univ`. A $C^\infty$ potential is finite and differentiable everywhere, as Definition 3.1 requires for $b$-smoothness.
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Definition 3.1, p.12

import Mathlib

open MeasureTheory
open scoped ContDiff NNReal

noncomputable section

namespace SongZhangKLS

/-- `W` is a **regular potential** of `µ` (Song, Zhang, *An O(1) Bound for the KLS Constant*,
arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c, Definition 3.1, p.12):
`dµ = e^{−W} dx` with `W ∈ C^∞(ℝⁿ)` finite, and for some `0 < a ≤ b < ∞` the measure is
`a`-strongly log-concave (`W(x) − a‖x‖²/2` convex) and `b`-smooth (`∇W` globally `b`-Lipschitz).

**Formalization Note.** `dx` is `volume` on `EuclideanSpace ℝ (Fin n)` (Lebesgue measure) and the
density is `ENNReal.ofReal (exp (−W x))`. `∇W` is Mathlib's `gradient W`. The constants `a, b` of
Definition 3.1 are existential and may depend on `µ`, as the paper states. -/
def IsRegularPotential {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (W : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ ∞ W ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-W x))) ∧
    ∃ (a : ℝ) (b : ℝ≥0), 0 < a ∧ a ≤ (b : ℝ) ∧
      ConvexOn ℝ Set.univ (fun x => W x - a / 2 * ‖x‖ ^ 2) ∧
      LipschitzWith b (gradient W)

/-- A measure `µ` on `ℝⁿ` is **regular** (Definition 3.1, p.12, of Song, Zhang,
arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c) if it has a regular potential:
`dµ = e^{−W}dx` with `W ∈ C^∞`, `a`-strongly log-concave and `b`-smooth for some `0 < a ≤ b < ∞`. -/
def IsRegular {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ W : EuclideanSpace ℝ (Fin n) → ℝ, IsRegularPotential μ W

end SongZhangKLS


