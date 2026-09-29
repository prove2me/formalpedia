-- Prove2me | Definitions.Def_landreman_integer_iota_family
-- name    : landreman_integer_iota_family
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T18:43:26.165992+00:00
-- url     : https://prove2.me/theorems/716d499d-9498-4fd7-9ab4-75891891ea90
-- title:
--   The integer-transform family: field, flux label, pressure and field-line coordinates
-- statement:
--   This file records, in Cartesian coordinates, the objects of the integer-transform family of analytic MHD equilibria.
--
--   Fix a parameter $\epsilon$ and set $a=\sqrt{1+\epsilon}$ and $b=\sqrt{1-\epsilon}$. For a point $x=(x_0,x_1,x_2)$ put
--
--   $$s=\frac{x_0^2}{a^2}+\frac{x_1^2}{b^2},\qquad
--   \rho = 1-(1-s)^2-4x_2^2,\qquad F=\sqrt{\rho},$$
--
--   and define the magnetic field
--
--   $$B=\left(\frac{2x_2x_0-(a/b)Fx_1}{s},\ \frac{2x_2x_1+(b/a)Fx_0}{s},\ 1-s\right),$$
--
--   on the open set $U_\epsilon=\{x:\rho>0\}$. With $Q=\tfrac12(x_0^2+x_1^2+4x_2^2)$ and the Bernoulli function $H=Q+\tfrac12|B|^2$, the flux label and the pressure are
--
--   $$\psi=\frac{H-1+\epsilon^2/2}{2},\qquad p=p_a-2\psi,$$
--
--   with $p_a$ an arbitrary constant, and the plasma domain is $\Omega_\delta=\{x\in U_\epsilon:\psi\le\delta\}$.
--
--   The file also records the field-line coordinates. For labels $(u,v)$, with $q^2=u^2+v^2$ and $L=\big((1+\sqrt{1-4q^2})/2\big)^{1/2}$, the position map is
--
--   $$r(u,v,\zeta)=\Big(a\big[L\cos\zeta+\tfrac{u\cos\zeta+v\sin\zeta}{L}\big],\ b\big[L\sin\zeta+\tfrac{v\cos\zeta-u\sin\zeta}{L}\big],\ v\cos 2\zeta-u\sin 2\zeta\Big),$$
--
--   the magnetic axis is $\gamma(\zeta)=\big(\sqrt{1-\epsilon^2}\cos\zeta,\ \sqrt{1-\epsilon^2}\sin\zeta,\ \tfrac{\epsilon}{2}\sin2\zeta\big)$, and rotation by an angle $t$ about the $z$ axis is recorded for the statement of non-axisymmetry.
--
--   Finally the complex **poloidal displacement** of a point from the axis is
--   $$\big(R-R_a\big)-i\big(x_2-Z_a\big),\qquad R=\sqrt{x_0^2+x_1^2},\quad R_a=\sqrt{1-\epsilon^2},\quad Z_a=\frac{\epsilon x_0x_1}{R^2},$$
--   where $Z_a$ is the elevation of the magnetic axis at the toroidal angle of the point, since $\tfrac{\epsilon}{2}\sin 2\phi=\epsilon x_0x_1/R^2$. Winding of this quantity along a field line is what measures the rotational transform.
--
--   **Formalization Note.** The definitions are total: outside $U_\epsilon$ the square root returns $0$ and the quotients by $s$ return the library's junk value at $s=0$, so every theorem about them carries the hypothesis that the point lies in $U_\epsilon$ or in $\Omega_\delta$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.1)-(2.4), (2.11), (2.12), (2.16)-(2.19), (2.23)

import Mathlib
import Definitions.Def_landreman_vector_calculus

namespace Landreman3DEquilibria

/-- `a = √(1 + ε)`, the first semiaxis parameter of the stretching. -/
noncomputable def aCoef (e : ℝ) : ℝ := Real.sqrt (1 + e)

/-- `b = √(1 - ε)`, the second semiaxis parameter of the stretching. -/
noncomputable def bCoef (e : ℝ) : ℝ := Real.sqrt (1 - e)

/-- `s = x²/a² + y²/b²`. -/
noncomputable def sFun (e : ℝ) (x : LVec) : ℝ :=
  x 0 ^ 2 / aCoef e ^ 2 + x 1 ^ 2 / bCoef e ^ 2

/-- The radicand `1 - (1 - s)² - 4 z²` appearing under the square root in `F`. -/
noncomputable def radicand (e : ℝ) (x : LVec) : ℝ := 1 - (1 - sFun e x) ^ 2 - 4 * x 2 ^ 2

/-- `F = √(1 - (1 - s)² - 4 z²)`. -/
noncomputable def FFun (e : ℝ) (x : LVec) : ℝ := Real.sqrt (radicand e x)

/-- The magnetic field of the integer-transform family. -/
noncomputable def Bfield (e : ℝ) (x : LVec) : LVec :=
  ![(2 * x 2 * x 0 - (aCoef e / bCoef e) * FFun e x * x 1) / sFun e x,
    (2 * x 2 * x 1 + (bCoef e / aCoef e) * FFun e x * x 0) / sFun e x,
    1 - sFun e x]

/-- The open domain `U_ε` on which the radicand is positive. -/
def domainU (e : ℝ) : Set LVec := {x | 0 < radicand e x}

/-- `Q = (x² + y² + 4 z²)/2`, the hydrodynamic pressure of the associated Euler flow. -/
noncomputable def Qfun (x : LVec) : ℝ := (x 0 ^ 2 + x 1 ^ 2 + 4 * x 2 ^ 2) / 2

/-- The Bernoulli function `H = Q + |B|²/2`. -/
noncomputable def Hfun (e : ℝ) (x : LVec) : ℝ := Qfun x + normSq (Bfield e x) / 2

/-- The flux label `ψ = (H - 1 + ε²/2)/2`. -/
noncomputable def psiFun (e : ℝ) (x : LVec) : ℝ := (Hfun e x - 1 + e ^ 2 / 2) / 2

/-- The scalar pressure `p = p_a - 2 ψ`. -/
noncomputable def pressure (e pa : ℝ) (x : LVec) : ℝ := pa - 2 * psiFun e x

/-- The toroidal plasma domain `Ω_δ = {x ∈ U_ε : ψ ≤ δ}`. -/
def domainOmega (e d : ℝ) : Set LVec := {x ∈ domainU e | psiFun e x ≤ d}

/-- `L`, determined by the field-line labels through `L² + q²/L² = 1`, `q² = u² + v²`. -/
noncomputable def Lfun (u v : ℝ) : ℝ :=
  Real.sqrt ((1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2)

/-- The position map `r(u, v, ζ)` of field-line coordinates. -/
noncomputable def posMap (e u v z : ℝ) : LVec :=
  ![aCoef e * (Lfun u v * Real.cos z + (u * Real.cos z + v * Real.sin z) / Lfun u v),
    bCoef e * (Lfun u v * Real.sin z + (v * Real.cos z - u * Real.sin z) / Lfun u v),
    v * Real.cos (2 * z) - u * Real.sin (2 * z)]

/-- The magnetic axis curve `γ(ζ)`. -/
noncomputable def axisCurve (e z : ℝ) : LVec :=
  ![Real.sqrt (1 - e ^ 2) * Real.cos z, Real.sqrt (1 - e ^ 2) * Real.sin z,
    e / 2 * Real.sin (2 * z)]

/-- Rotation of Cartesian space by the angle `t` about the `z` axis. -/
noncomputable def rotZ (t : ℝ) (x : LVec) : LVec :=
  ![Real.cos t * x 0 - Real.sin t * x 1, Real.sin t * x 0 + Real.cos t * x 1, x 2]

/-- The complex poloidal displacement of a point from the magnetic axis: its real part is
`R - R_a` with `R = √(x² + y²)` and `R_a = √(1 - ε²)`, and its imaginary part is
`-(z - Z_a)` with the axis elevation `Z_a = (ε/2) sin 2φ = ε x y / R²` at the same
toroidal angle `φ`. -/
noncomputable def poloidalDisp (e : ℝ) (x : LVec) : ℂ :=
  ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt (1 - e ^ 2) : ℝ) : ℂ) -
    Complex.I * ((x 2 - e * x 0 * x 1 / (x 0 ^ 2 + x 1 ^ 2) : ℝ) : ℂ)

end Landreman3DEquilibria


