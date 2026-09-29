-- Prove2me | Definitions.Def_AvramDividend_BailOut_ScaleFunction
-- name    : AvramDividend_BailOut_ScaleFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:01:52.422104+00:00
-- url     : https://prove2.me/theorems/5b2bf2a7-5ece-437b-9e71-9a242de5e10e
-- title:
--   The $q$-scale functions $W^{(q)}$, $\overline W^{(q)}$, $Z^{(q)}$, $\overline Z^{(q)}$
-- statement:
--   Let $(c,\sigma,\nu)$ be a Lévy triplet without positive jumps with Laplace exponent $\psi$, and let $q\ge 0$. Write $\Phi(q)$ for the largest root $\theta\ge0$ of $\psi(\theta)=q$ (the right inverse of $\psi$).
--
--   A function $W=W^{(q)}:\mathbb R\to\mathbb R$ is the **$q$-scale function** if $W(y)=0$ for $y<0$, $W\ge 0$, $W$ is continuous and nondecreasing on $[0,\infty)$, and
--
--   $$\int_0^\infty e^{-\theta y}\,W^{(q)}(y)\,dy=\frac{1}{\psi(\theta)-q}\qquad\text{for every }\theta>\Phi(q).$$
--
--   These properties determine $W^{(q)}$ uniquely. From it one builds
--
--   $$\overline W^{(q)}(y)=\int_0^y W^{(q)}(z)\,dz,\qquad Z^{(q)}(y)=1+q\,\overline W^{(q)}(y),\qquad \overline Z^{(q)}(y)=\int_0^y Z^{(q)}(z)\,dz .$$
--
--   For $y<0$ these give $\overline W^{(q)}(y)=0$, $Z^{(q)}(y)=1$ and $\overline Z^{(q)}(y)=y$.
--
--   The scale functions express every fluctuation identity and every value function of the paper.
--
--   **Formalization Note** $\Phi(q)$ is the real supremum of the root set $\{\theta\ge0:\psi(\theta)=q\}$. Under the standing assumptions (no monotone paths) and $q\ge 0$ this set is nonempty and bounded, so the supremum is the largest root. The paper prints the Laplace transform (3.4) with $e^{-\theta x}$ inside a $dy$-integral; the variable is $y$. $W$ is not assumed continuous at $0$ from the left: in bounded variation $W(0)=1/d>0$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 4 (Φ), p. 5 (Section 3.2, eq. (3.4)), p. 6 (Z^(q) and the antiderivative), p. 8 (Section 3.4, the antiderivative of Z^(q))

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

namespace LevyTriplet

/-- `Φ(q)`, the largest root of `ψ(θ) = q` on `[0, ∞)` (the right inverse of `ψ`, p. 4).
Under the standing assumptions (no monotone paths) the root set is nonempty and bounded for
`q ≥ 0`, so the real supremum is the largest root. -/
noncomputable def Phi (T : LevyTriplet) (q : ℝ) : ℝ :=
  sSup {θ : ℝ | 0 ≤ θ ∧ T.laplaceExponent θ = q}

/-- `W` is the `q`-scale function of the triplet `T` (p. 5, (3.4)): `W(y) = 0` for `y < 0`,
`W ≥ 0`, `W` is continuous and nondecreasing on `[0, ∞)`, and
`∫_0^∞ e^{-θ y} W(y) dy = 1/(ψ(θ) - q)` for every `θ > Φ(q)`. These properties determine `W`
uniquely (Laplace inversion and right-continuity). -/
def IsScaleFunction (T : LevyTriplet) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ y, y < 0 → W y = 0) ∧ (∀ y, 0 ≤ W y) ∧ ContinuousOn W (Set.Ici 0) ∧
    MonotoneOn W (Set.Ici 0) ∧
    ∀ θ : ℝ, T.Phi q < θ →
      ∫ y in Set.Ioi (0 : ℝ), Real.exp (-θ * y) * W y = 1 / (T.laplaceExponent θ - q)

end LevyTriplet

/-- `W̄(y) = ∫_0^y W(z) dz` (p. 6); equal to `0` for `y < 0` when `W` vanishes there. -/
noncomputable def Wbar (W : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..y, W z

/-- `Z(y) = 1 + q W̄(y)` (p. 6); equal to `1` for `y < 0`. -/
noncomputable def Zq (q : ℝ) (W : ℝ → ℝ) (y : ℝ) : ℝ :=
  1 + q * Wbar W y

/-- `Z̄(y) = ∫_0^y Z(z) dz = y + q ∫_0^y ∫_0^z W(w) dw dz` (p. 8); equal to `y` for `y < 0`. -/
noncomputable def Zbar (q : ℝ) (W : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..y, Zq q W z

end AvramDividend.BailOut


