-- Prove2me | Definitions.Def_DbarRegularity_Setting
-- name    : DbarRegularity_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-11T21:52:04.602051+00:00
-- url     : https://prove2.me/theorems/7d77ad74-fe1f-497e-be66-34208848af26
-- title:
--   The maximal function, cubes, the Cauchy–Riemann operator and smooth Sobolev norms
-- statement:
--   Four basic objects for the $L^p$ theory of singular integrals on $\mathbb{R}^d$ and of the Cauchy–Riemann operator on $\mathbb{C}$.
--
--   1. **Hardy–Littlewood maximal function** (E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, § 1.1, formula (2)). For $f:\mathbb{R}^d\to\mathbb{C}$ and $x\in\mathbb{R}^d$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{m(B(x,r))}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $m$ is Lebesgue measure.
--   2. **Closed cube.** For $a\in\mathbb{R}^d$ and $s\in\mathbb{R}$, $Q(a,s)=\{x\in\mathbb{R}^d: a_i\le x_i\le a_i+s\text{ for all }i\}$.
--   3. **Cauchy–Riemann operator** (C. Abbas, H. Hofer, *Holomorphic Curves and Global Questions in Contact Geometry*, § 4.2). For a map $\varphi:\mathbb{C}\to E$ into a complex normed space and $z=s+it$,
--   $$\bar\partial\varphi=\frac{\partial\varphi}{\partial s}+i\,\frac{\partial\varphi}{\partial t},$$
--   without the factor $\tfrac12$.
--   4. **Sobolev norm of a smooth map.** For $k\in\mathbb{N}$, $p\in[1,\infty]$, $U\subset\mathbb{C}$ and $\varphi:\mathbb{C}\to E$,
--   $$\|\varphi\|_{W^{k,p}(U)}=\sum_{j=0}^{k}\big\|D^j\varphi\big\|_{L^p(U)},$$
--   where $D^j\varphi(z)$ is the $j$-th Fréchet derivative, a $j$-linear map $\mathbb{C}^j\to E$ over $\mathbb{R}$, measured in the operator norm.
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with its Lebesgue measure `volume`. `maximalFunction f x` is `⨆ r > 0, (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ`, valued in `ℝ≥0∞`, so $Mf(x)=\infty$ is allowed. `dbar φ z = fderiv ℝ φ z 1 + I • fderiv ℝ φ z I`: the partial derivatives $\partial_s\varphi$, $\partial_t\varphi$ are the real Fréchet derivative applied to $1$ and $i$. `sobolevNorm k p U φ` is `∑ j ∈ range (k + 1), eLpNorm (iteratedFDeriv ℝ j φ) p (volume.restrict U)`, valued in `ℝ≥0∞`. It is equivalent, up to constants depending on $k$ and $p$, to the norm built from the partial derivatives $\partial_s^a\partial_t^b\varphi$, $a+b\le k$; it is used only in an estimate with an unspecified constant.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter I, § 1.1, formula (2), p. 4; C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, pp. 100–101

import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Complex.Basic

/-!
# Basic objects for the `L^p` theory of the Cauchy–Riemann operator

* `maximalFunction f` is the Hardy–Littlewood maximal function of `f : ℝ^d → ℂ`
  (E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  1970, Chapter I, § 1.1, formula (2)), with values in `[0, ∞]`.
* `closedCube a s` is the closed cube `∏ᵢ [aᵢ, aᵢ + s]` in `ℝ^d`.
* `dbar φ` is the Cauchy–Riemann operator `∂φ/∂s + i ∂φ/∂t` on maps `φ : ℂ → E`, `z = s + i t`,
  without the factor `1/2` (C. Abbas, H. Hofer, *Holomorphic Curves and Global Questions in
  Contact Geometry*, Birkhäuser 2019, § 4.2).
* `sobolevNorm k p U φ` is the `W^{k,p}(U)` norm `∑_{j ≤ k} ‖D^j φ‖_{L^p(U)}` of a map
  `φ : ℂ → E`, where `D^j φ` is the `j`-th Fréchet derivative and `‖·‖` its operator norm.
-/

namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal

noncomputable section

/-- The Hardy–Littlewood maximal function
`M f (x) = sup_{r > 0} (1 / |B(x, r)|) ∫_{B(x, r)} |f(y)| dy`, valued in `[0, ∞]`. -/
def maximalFunction {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ

/-- The closed cube `{x | ∀ i, aᵢ ≤ xᵢ ≤ aᵢ + s}` in `ℝ^d` with corner `a` and side length `s`. -/
def closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ a i + s}

/-- The Cauchy–Riemann operator `∂̄φ = ∂φ/∂s + i ∂φ/∂t` for `φ : ℂ → E` and `z = s + i t`. -/
def dbar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ φ z 1 + Complex.I • fderiv ℝ φ z Complex.I

/-- The `W^{k,p}(U)` norm `∑_{j = 0}^{k} ‖D^j φ‖_{L^p(U)}` of `φ : ℂ → E`, where `D^j φ` is the
`j`-th Fréchet derivative over `ℝ`, measured in the operator norm. -/
def sobolevNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (p : ℝ≥0∞)
    (U : Set ℂ) (φ : ℂ → E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j φ) p (volume.restrict U)

end

end DbarRegularity


