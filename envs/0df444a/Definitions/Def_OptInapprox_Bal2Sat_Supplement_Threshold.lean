-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Supplement_Threshold
-- name    : OptInapprox_Bal2Sat_Supplement_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:54:11.594873+00:00
-- url     : https://prove2.me/theorems/c0925edb-a4cd-4c68-9b99-44c07e6b884b
-- title:
--   Theorem 5 and Theorem 7 — threshold functions, Φ, Φ⁻¹ and the Gaussian isoperimetric function
-- statement:
--   On the cube $\{-1,1\}^n$, with the published convention TRUE $\mapsto -1$, the threshold function with coefficients $a\in\mathbb R^n$ is
--
--   $$f_a(x)=\operatorname{sgn}(a_1x_1+\cdots+a_nx_n).$$
--
--   At a zero linear form the value is $-1$; the theorems that use $f_a$ assume the linear form never vanishes, as in footnote 1 on p. 22. $\Phi(x)=\Pr[X\le x]$ is the standard Gaussian distribution function, $\Phi^{-1}(\mu)$ is the unique $t$ with $\Phi(t)=\mu$ for $0<\mu<1$, and the Gaussian isoperimetric function is $U(\mu)=\varphi(\Phi^{-1}(\mu))$ for $0<\mu<1$ with $U(0)=U(1)=0$, where $\varphi$ is the published standard Gaussian density.
--
--   **Formalization Note** $\Phi^{-1}$ returns the placeholder $0$ outside $(0,1)$; $U$ takes its limiting values $0$ there explicitly.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 12–13, 22, Theorems 5 and 7, footnote 1

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube
import Definitions.Def_OptInapprox_Orthant_Setting

namespace OptInapprox.Bal2Sat.Supplement

noncomputable section
open MeasureTheory ProbabilityTheory

/-- The threshold function `f(x) = sgn(a₁x₁ + ⋯ + aₙxₙ)` of Theorem 5 (p. 12), on the cube
`{-1,1}ⁿ` read through the published `pm` (TRUE ↦ −1). The value at a zero linear form is
`-1`; Theorem 5 only uses linear forms that never vanish (footnote 1, p. 22). -/
def thresholdFn {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  if 0 < ∑ i, a i * OptInapprox.MaxCut.pm (x i) then 1 else -1

/-- The Gaussian distribution function `Φ(x) = Pr[X ≤ x]`, `X` standard normal (Theorem 7). -/
def gaussCdf (x : ℝ) : ℝ := (gaussianReal 0 1 (Set.Iic x)).toReal

open scoped Classical in
/-- `Φ⁻¹(μ)`: the point `t` with `Φ(t) = μ`. It exists, and is unique, exactly when
`0 < μ < 1`; otherwise the value is the placeholder `0`. -/
def gaussCdfInv (μ : ℝ) : ℝ :=
  if h : ∃ t : ℝ, gaussCdf t = μ then Classical.choose h else 0

/-- The Gaussian isoperimetric function `U(μ) = φ(Φ⁻¹(μ))` on `[0,1]` (Theorem 7, p. 13), with
the boundary values `U(0) = U(1) = 0` of the limits `φ(∓∞) = 0`. -/
def gaussIso (μ : ℝ) : ℝ :=
  if 0 < μ ∧ μ < 1 then OptInapprox.Orthant.phi (gaussCdfInv μ) else 0

end
end OptInapprox.Bal2Sat.Supplement


