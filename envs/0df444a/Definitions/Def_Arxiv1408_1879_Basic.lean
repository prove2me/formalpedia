-- Prove2me | Definitions.Def_Arxiv1408_1879_Basic
-- name    : Arxiv1408_1879_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T11:27:43.195135+00:00
-- url     : https://prove2.me/theorems/abca5719-fd80-46ac-9f1e-d320d8fe3357
-- title:
--   Two-way parabolic integral equation: Green's functions, surface operators L and R, operator series
-- statement:
--   Objects of Sections 2, 3 and 4.1 of Spivack and Rath Spivack (2015).
--
--   1. **Constants.** For a wavenumber $k>0$, $\alpha=\tfrac12\sqrt{i/(2\pi k)}$ (principal square root). For an angle of incidence $\theta$ measured from the vertical, $S=\sin\theta-1$ (eq. 5).
--   2. **Parabolic Green's functions.** The one-way function is $G_p(x,z;x',z')=\alpha\,(x-x')^{-1/2}\exp\big[ik(z-z')^2/(2(x-x'))\big]$ for $x'<x$ and $0$ otherwise. The two-way function $G$ of eq. (6) equals $G_p$ for $x'<x$. For $x'\ge x$ it equals $\alpha\,(x'-x)^{-1/2}\exp\big[ik(z-z')^2/(2(x'-x))\big]\exp[2ik(x'-x)]$.
--   3. **Improper integrals.** $\int_a^\infty f$ is $\lim_{T\to\infty}\int_a^T f$. The function $f$ is improperly integrable from $a$ if it is integrable on every $[a,T]$ with $T\ge a$ and this limit exists.
--   4. **Surface operators (Section 3.1).** For a surface $z=h(x)$, a surface source $f$ and a point $(x,z)$, with $r'=(x',h(x'))$:
--   $$Lf(x,z)=\int_0^x G\big((x,z),r'\big)f(x')\,dx',\qquad Rf(x,z)=\int_x^\infty G\big((x,z),r'\big)f(x')\,dx'.$$
--   The two-way scattered-field integral of eq. (7) is $\int_0^\infty G\big((x,z),r'\big)f(x')\,dx'$.
--   5. **Flat-surface operators (eq. 20).** These are $L$ and $R$ for $h=0$, on the mean plane $z=0$: $L_0f(x)=\alpha\int_0^x(x-x')^{-1/2}f(x')\,dx'$ and $R_0f(x)=\alpha\int_x^\infty(x'-x)^{-1/2}e^{2ik(x'-x)}f(x')\,dx'$.
--   6. **Operator series (eqs. 12, 13, 15).** For an invertible bounded operator $L$ and a bounded operator $R$ on a complex normed space, the $n$-th term is $\varphi_n=(L^{-1}R)^nL^{-1}\psi_i$, and the series (12) is $\sum_n(-1)^n\varphi_n$. The first approximation is $\tilde\psi=L^{-1}\psi_i$ and the correction is $C=L^{-1}RL^{-1}\psi_i$.
--   7. **Mean-plane field (eq. 16).** For an incident field $\psi_i(x,z)$, a surface $h$ and a surface source $u=\partial\psi/\partial z$, the mean-plane field is
--   $$\Psi[u](x)=-\psi_i(x,h(x))-h(x)\Big[u(x)-\partial_z\psi_i(x,h(x))\Big]-\tfrac12h(x)^2\,\partial_z^2\psi_i(x,0).$$
--   This is the right-hand side of (16) without its $O(\sigma^3)$ remainder.
--
--   **Formalization Note** The kernel of $G$ is singular at $x'=x$. On that null set $G$ is given the value $0$, and no integral depends on it. The phase factor for $x'\ge x$ is $\exp[+2ik(x'-x)]$, as in the display (6). The sentence after (6) writes $\exp[-2ik(x'-x)]$. All integrals to $+\infty$ are improper limits, because for the plane-wave data of Section 4 they converge only conditionally. $R_0$ is defined as the flat-surface form of $R$, so it carries the factor $e^{2ik(x'-x)}$ of eq. (6), which the printed eq. (20) omits.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), Sections 2, 3.1, 3.2 and 4.1, eqs. (5), (6), (7)-(10), (12)-(16), (20)

import Mathlib

/-!
M. Spivack and O. Rath Spivack, *Rough surface backscatter and statistics via extended
parabolic integral equation*, arXiv:1408.1879v2 (2015): the constant `α` and the one-way and
two-way parabolic Green's functions (Section 2 and Section 3.1, eq. (6)), the surface operators
`L`, `R` and the scattered-field integral (Section 3.1, eqs. (7)-(10)), their flat-surface forms
(Section 4.1, eq. (20)), the terms of the operator series (Section 3.2, eqs. (12)-(15)) and the
second-order mean-plane field (Section 4.1, eq. (16)).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv1408_1879

/-- Section 2, after the display defining `G_p` (PDF p. 4): `α = (1/2) √(i / (2πk))`, with the
principal square root. -/
def alpha (k : ℝ) : ℂ := (1 / 2) * (Complex.I / (2 * Real.pi * k)) ^ (1 / 2 : ℂ)

/-- Eq. (5) (PDF p. 4): `S = sin θ - 1`, where `θ` is the angle of incidence from the vertical. -/
def S (θ : ℝ) : ℝ := Real.sin θ - 1

/-- Section 2, unnumbered display after eq. (3) (PDF p. 4): the one-way parabolic Green's function
`G_p(x,z;x',z') = α (x-x')^{-1/2} exp[ik(z-z')²/(2(x-x'))]` for `x' < x`, and `0` otherwise. -/
def greenOneWay (k x z x' z' : ℝ) : ℂ :=
  if x' < x then
    alpha k * ((1 / Real.sqrt (x - x') : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((k * (z - z') ^ 2 / (2 * (x - x')) : ℝ) : ℂ))
  else 0

/-- Eq. (6) (Section 3.1, PDF p. 5): the two-way parabolic Green's function `G(x,z;x',z')`, equal
to `α (x-x')^{-1/2} exp[ik(z-z')²/(2(x-x'))]` for `x' < x` and to
`α (x'-x)^{-1/2} exp[ik(z-z')²/(2(x'-x))] exp[2ik(x'-x)]` for `x' ≥ x` (the sign of the display).
At the single point `x' = x`, where the paper's kernel is singular, the value is `0`. -/
def greenTwoWay (k x z x' z' : ℝ) : ℂ :=
  if x' < x then
    alpha k * ((1 / Real.sqrt (x - x') : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((k * (z - z') ^ 2 / (2 * (x - x')) : ℝ) : ℂ))
  else
    alpha k * ((1 / Real.sqrt (x' - x) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((k * (z - z') ^ 2 / (2 * (x' - x)) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((2 * k * (x' - x) : ℝ) : ℂ))

/-- The integrals `∫_a^∞` of eqs. (7), (8) and of the operator `R` (Section 3.1, PDF p. 5) as
improper integrals: `f` is integrable on every `[a, T]` and `∫_a^T f` converges as `T → ∞`. -/
def ImproperIntegrable (f : ℝ → ℂ) (a : ℝ) : Prop :=
  (∀ T, a ≤ T → IntervalIntegrable f volume a T) ∧
    ∃ I : ℂ, Tendsto (fun T => ∫ t in a..T, f t) atTop (𝓝 I)

/-- The value `∫_a^∞ f = lim_{T→∞} ∫_a^T f` of an improper integral (meaningful when
`ImproperIntegrable f a`). -/
def improperIntegral (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  limUnder atTop (fun T => ∫ t in a..T, f t)

/-- Section 3.1, definition after eq. (10) (PDF p. 5): `L f(x,z) = ∫_0^x G(r, r') f(x') dx'` with
`r = (x,z)` and `r' = (x', h(x'))` on the surface `h`. -/
def leftOp (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (x z : ℝ) : ℂ :=
  ∫ x' in (0 : ℝ)..x, greenTwoWay k x z x' (h x') * f x'

/-- Section 3.1, definition after eq. (10) (PDF p. 5): `R f(x,z) = ∫_x^∞ G(r, r') f(x') dx'` with
`r = (x,z)` and `r' = (x', h(x'))`, as an improper integral. -/
def rightOp (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (x z : ℝ) : ℂ :=
  improperIntegral (fun x' => greenTwoWay k x z x' (h x') * f x') x

/-- Eq. (7) (Section 3.1, PDF p. 5): the two-way scattered-field integral
`∫_0^∞ G(r, r') f(x') dx'`, `r = (x,z)`, `r' = (x', h(x'))`, for a surface source `f = ∂ψ/∂z`. -/
def twoWayField (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (x z : ℝ) : ℂ :=
  improperIntegral (fun x' => greenTwoWay k x z x' (h x') * f x') 0

/-- Eq. (20) (Section 4.1, PDF p. 8): `L_0`, the deterministic (flat surface, `h = 0`) form of `L`,
evaluated on the mean plane: `L_0 f(x) = α ∫_0^x (x-x')^{-1/2} f(x') dx'`. -/
def leftOpFlat (k : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  leftOp k (fun _ => 0) f x 0

/-- Eq. (20) (Section 4.1, PDF p. 8): `R_0`, the deterministic (flat surface, `h = 0`) form of `R`,
evaluated on the mean plane. With `G` of eq. (6) this is
`R_0 f(x) = α ∫_x^∞ (x'-x)^{-1/2} exp[2ik(x'-x)] f(x') dx'`. -/
def rightOpFlat (k : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  rightOp k (fun _ => 0) f x 0

section Series

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Eq. (12) (Section 3.2, PDF p. 6): the `n`-th term `(L⁻¹R)ⁿ L⁻¹ ψ_i` of the series
`∂ψ/∂z = [L⁻¹ - L⁻¹RL⁻¹ + (L⁻¹R)²L⁻¹ - ...] ψ_i`, for an invertible operator `L` and an
operator `R` on a normed space. The series is `∑ (-1)ⁿ (L⁻¹R)ⁿ L⁻¹ ψ_i`. -/
def seriesTerm (L : E ≃L[ℂ] E) (R : E →L[ℂ] E) (ψi : E) (n : ℕ) : E :=
  (((L.symm : E →L[ℂ] E).comp R) ^ n) (L.symm ψi)

/-- Eq. (13) (Section 3.2, PDF p. 6): the first approximation `ψ̃ = L⁻¹ ψ_i`. -/
def firstApprox (L : E ≃L[ℂ] E) (ψi : E) : E := L.symm ψi

/-- Eq. (15) (Section 3.2, PDF p. 6): the correction term `C = L⁻¹ R L⁻¹ ψ_i`. -/
def correctionTerm (L : E ≃L[ℂ] E) (R : E →L[ℂ] E) (ψi : E) : E := L.symm (R (L.symm ψi))

end Series

/-- Eq. (16) (Section 4.1, PDF p. 8) without its `O(σ³)` remainder: the scattered field on the mean
plane `z = 0` for an incident field `ψ_i(x,z)`, surface `h` and surface source `u = ∂ψ/∂z`,
`-ψ_i(x,h) - h [u - ∂ψ_i/∂z (x,h)] - (h²/2) ∂²ψ_i/∂z² (x,0)`. The point `(x,h)` of the
`∂ψ_i/∂z` term is the one printed in eq. (18). -/
def meanPlaneField (ψi : ℝ → ℝ → ℂ) (h : ℝ → ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  -ψi x (h x) - (h x : ℂ) * (u x - deriv (ψi x) (h x)) -
    (h x : ℂ) ^ 2 / 2 * iteratedDeriv 2 (ψi x) 0

end Arxiv1408_1879


