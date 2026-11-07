-- Prove2me | Definitions.Def_SYKCavity_Saddle
-- name    : SYKCavity_Saddle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:29.930965+00:00
-- url     : https://prove2.me/theorems/3bc1593d-0074-4de9-982b-e197d0865457
-- title:
--   Positive spectral kernels $G_\mu$, the saddle equations (3.21) and the SYK saddle $G_*$
-- statement:
--   For a finite positive Borel measure $\mu$ on $[0,\infty)$ let
--   $$G_\mu(t)=\int_0^\infty\frac{\cosh(x(1/2-t))}{2\cosh(x/2)}\,\mu(dx),\qquad0\le t\le1\qquad(D.1)$$
--   (and its continuation $G_\mu(z)$ to complex $z$). It is a **normalized positive spectral kernel** when $\mu$ is a probability measure. With $\omega_n=(2n+1)\pi$ and $\hat f(n)=\int_0^1e^{i\omega_nt}f(t)\,dt$ for $n\in\mathbb Z$, the **SYK saddle-point equations** are
--   $$\Sigma_*(t)=\beta^2G_*(t)^3,\qquad\hat G_*(n)=\bigl(-i\omega_n-\hat\Sigma_*(n)\bigr)^{-1}.\qquad(3.21)$$
--   `IsSaddle β μ` says that $G_\mu$ solves them; `saddle β` is the solution $\mu_{*,\beta}$ (Lemma 40: it exists and is unique for $\beta\ge0$), and $G_*=G_{\mu_{*,\beta}}$ on $[0,1]$.
--
--   The two-time kernel is $G_*(u,v)=G_*(u-v)$, extended antisymmetrically and antiperiodically ($G_*(u+1,v)=-G_*(u,v)$), with $G_*(u,u)=0$. Its ordered limits $\lim_{\varepsilon\downarrow0}G_*(x+\varepsilon\delta)$ at $x\in\mathbb Z$ are $\pm1/2$ (with the antiperiodic sign), the one-sided endpoint values $G_*(0^+)=G_*(1^-)=1/2$.
--
--   $G_*$ is the point around which the algorithm expands; every later object (the ladder operator, the centered moments, $B(t)$) is built from it.
--
--   **Formalization Note** Measures live on $\mathbb R$ with $\mu((-\infty,0))=0$. When no solution exists `saddle β` is $\delta_0$ (never used: Lemma 40 gives existence). Since $\hat G_\mu(n)\ne0$ for a probability measure, the inverse in (3.21) is never satisfied through $0^{-1}=0$.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (3.21) and the two-time convention, p.23; (3.7), p.21; (D.1), p.88; (5.5), p.33

import Mathlib

open MeasureTheory

namespace SYKCavity

/-!
# Positive spectral kernels, the SYK saddle-point equations and the saddle `G*`

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): saddle equations (3.21) and the
two-time convention, p.23; (3.7), p.21; Appendix D, (D.1), p.88; (5.5), p.33.

**Formalization Note.**
* `Gmu μ t = ∫ cosh(x(1/2 − t)) / (2 cosh(x/2)) μ(dx)` is (D.1). A *normalized positive spectral
  kernel* is `Gmu μ` for a probability measure `μ` on `[0, ∞)`; measures are taken on `ℝ` with
  `μ (−∞, 0) = 0`. `GmuC μ z` is the same integral with complex `z` (used for `G*(it)` in (5.1); for
  real `t` the integrand has modulus `≤ 1/2`).
* `ω n = (2n+1)π` for every `n ∈ ℤ`, and `fourier f n = ∫_0^1 e^{iω_n t} f(t) dt`, p.23.
* `IsSaddle β μ`: `μ` is a probability measure on `[0, ∞)` and `G = Gmu μ` solves (3.21):
  `Σ(t) = β² G(t)³` on `[0, 1]` and `Ĝ(n) = (−iω_n − Σ̂(n))⁻¹` for every `n ∈ ℤ`. (For a probability
  measure `Ĝ(n) ≠ 0`, so a vanishing bracket never satisfies the equation through `0⁻¹ = 0`.)
* `saddle β` is a solution chosen by `Classical.choose` when one exists (Lemma 40 asserts that exactly
  one exists for every `β ≥ 0`), and `δ₀` otherwise; `Gstar β = Gmu (saddle β)` on `[0, 1]`, and
  `GstarC β = GmuC (saddle β)` is its complex continuation.
* The two-time kernel `G*(u, v) = G*(u − v)` is antisymmetric and antiperiodic, p.21 and p.23:
  `gExt β x = (−1)^{⌊x⌋} G*(fract x)` for `x ∉ ℤ` and `gExt β x = 0` for `x ∈ ℤ` (the page's
  `G*(u, u) = 0`; at `x ∈ ℤ` the two one-sided values `±(−1)^x/2` average to `0`).
* `gOrd β x δ` is the ordered limit `lim_{ε↓0} G*(x + εδ)` used by the ordered coincident-time
  prescription of Lemma 42 (p.95): at `x = n ∈ ℤ` it is `(−1)^n G*(0+)` for `δ > 0` and
  `(−1)^{n−1} G*(1−)` for `δ < 0` (and `0` for `δ = 0`); off `ℤ` it is `gExt β x`.
-/

/-- `G_μ(t) = ∫ cosh(x(1/2 − t)) / (2 cosh(x/2)) μ(dx)`, (D.1). -/
noncomputable def Gmu (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, Real.cosh (x * (1 / 2 - t)) / (2 * Real.cosh (x / 2)) ∂μ

/-- The complex continuation `G_μ(z) = ∫ cosh(x(1/2 − z)) / (2 cosh(x/2)) μ(dx)`. -/
noncomputable def GmuC (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x, Complex.cosh ((x : ℂ) * (1 / 2 - z)) / (2 * Complex.cosh ((x : ℂ) / 2)) ∂μ

/-- The fermionic Matsubara frequency `ω_n = (2n+1)π`. -/
noncomputable def omega (n : ℤ) : ℝ := (2 * n + 1) * Real.pi

/-- `f̂(n) = ∫_0^1 e^{iω_n t} f(t) dt`, p.23. -/
noncomputable def fourier (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * (omega n : ℂ) * t) * f t

/-- `μ` is a normalized positive spectral solution of the saddle-point equations (3.21). -/
def IsSaddle (β : ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
    ∀ n : ℤ, fourier (fun t => ((Gmu μ t : ℝ) : ℂ)) n =
      (-(Complex.I * (omega n : ℂ)) - fourier (fun t => ((β ^ 2 * Gmu μ t ^ 3 : ℝ) : ℂ)) n)⁻¹

open Classical in
/-- The spectral measure `μ*,β` of the saddle: a solution if one exists, else `δ₀`. -/
noncomputable def saddle (β : ℝ) : Measure ℝ :=
  if h : ∃ μ, IsSaddle β μ then h.choose else Measure.dirac 0

/-- `G*(t)` on `[0, 1]`, the positive-time branch of the saddle. -/
noncomputable def Gstar (β : ℝ) (t : ℝ) : ℝ := Gmu (saddle β) t

/-- `G*(z)`, the complex continuation of the positive-time branch. -/
noncomputable def GstarC (β : ℝ) (z : ℂ) : ℂ := GmuC (saddle β) z

/-- The antisymmetric, antiperiodic extension: `G*(u, v) = gExt β (u − v)`, `0` on `u − v ∈ ℤ`. -/
noncomputable def gExt (β : ℝ) (x : ℝ) : ℝ :=
  if Int.fract x = 0 then 0 else (-1 : ℝ) ^ ⌊x⌋ * Gstar β (Int.fract x)

/-- The ordered limit `lim_{ε↓0} G*(x + εδ)` of the two-time kernel. -/
noncomputable def gOrd (β : ℝ) (x δ : ℝ) : ℝ :=
  if Int.fract x = 0 then
    (if 0 < δ then (-1 : ℝ) ^ ⌊x⌋ * Gstar β 0
     else if δ < 0 then -((-1 : ℝ) ^ ⌊x⌋ * Gstar β 1) else 0)
  else gExt β x

end SYKCavity


