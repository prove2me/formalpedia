-- Prove2me | Definitions.Def_SKWeakPoincare_IsWienerMeasure
-- name    : SKWeakPoincare_IsWienerMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:19.011202+00:00
-- url     : https://prove2.me/theorems/2387fd52-af7b-4bd2-8de2-0a702a83ffc8
-- title:
--   Wiener measure on $C([0,T];\mathbb R^n)$ and the quantile function
-- statement:
--   **Wiener measure** $\gamma$ on $C([0,T];\mathbb R^n)$ is the law of the path $(B_t)_{0\le t\le T}$ of a standard Brownian motion in $\mathbb R^n$ started at zero. The **quantile function** of a real function $F$ under $\gamma$ is
--   $$
--   Q_F(v)=\inf\{a\in\mathbb R:\gamma[F\le a]\ge v\},\qquad 0<v<1.
--   $$
--
--   Wiener measure is the reference law of the driving paths of stochastic localization (Lemmas 3.5 and 6.1).
--
--   **Formalization Note** Mathlib does not construct Wiener measure, so `IsWienerMeasure T n γ` says that $\gamma$ is the push-forward of a measurable path-valued map on some probability space whose paths are those of a standard Brownian motion (`SKAnnealing.Sampling.IsStdBrownian`). Requiring every path to be continuous and the map measurable picks a continuous modification. All such laws coincide, because finite-dimensional laws determine a law on the separable space $C([0,T];\mathbb R^n)$, so $\gamma$ is unique. Brownian paths start at $0$ almost surely, so $\gamma(C_0)=1$.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Section 3.2, p.15 (Wiener measure γ); p.16 (quantile function Q_Z(v))

import Mathlib
import Definitions.Def_SKAnnealing_Sampling_IsStdBrownian
import Definitions.Def_SKWeakPoincare_PathSpace

open MeasureTheory SKAnnealing.Sampling
open scoped NNReal

namespace SKWeakPoincare

/-- `γ` is **Wiener measure** on `C([0, T]; ℝ^n)`: the law of the path `(B_t)_{0 ≤ t ≤ T}` of a
standard Brownian motion in `ℝ^n` started at zero.
Hou–Liu–Yu, arXiv:2610.09882, Section 3.2, p. 15 ("Wiener measure `γ` is the law on this space of a
standard Brownian motion in `ℝ^n` starting at zero").

**Formalization Note.** Mathlib does not construct Wiener measure, so `γ` is characterised as the
push-forward `P.map Wp` of a measurable path-valued map `Wp`, on some probability space, whose paths
are those of a standard Brownian motion `B` (`SKAnnealing.Sampling.IsStdBrownian`: independent
Mathlib `IsBrownianReal` coordinates). Taking `Wp` with every path continuous and measurable is the
choice of a continuous modification; all such laws coincide (the finite-dimensional laws determine a
law on the separable space `C([0, T]; ℝ^n)`), so `γ` is unique. Brownian paths start at `0` almost
surely, so `γ` is carried by `C₀([0, T]; ℝ^n)`. -/
def IsWienerMeasure (T : ℝ) (n : ℕ) (γ : Measure (PathSpace T n)) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → (Fin n → ℝ))
    (Wp : Ω → PathSpace T n),
    IsProbabilityMeasure P ∧ IsStdBrownian B P ∧ Measurable Wp ∧
    (∀ ω (s : Set.Icc (0 : ℝ) T), Wp ω s = WithLp.toLp 2 (B ⟨(s : ℝ), s.2.1⟩ ω)) ∧
    γ = P.map Wp

/-- The **quantile function** `Q_F(v) = inf{a ∈ ℝ : γ[F ≤ a] ≥ v}` of a real function `F` under a
measure `γ`. Hou–Liu–Yu, arXiv:2610.09882, p. 16 (defined for `0 < v < 1`).

**Formalization Note.** For a probability measure `γ`, a measurable `F` and `0 < v < 1` the set is
nonempty and bounded below, so the real `sInf` is the paper's infimum. -/
noncomputable def quantile {X : Type*} [MeasurableSpace X] (γ : Measure X) (F : X → ℝ) (v : ℝ) : ℝ :=
  sInf {a : ℝ | ENNReal.ofReal v ≤ γ {ω | F ω ≤ a}}

end SKWeakPoincare


