-- Prove2me | Definitions.Def_CelestialHolography_LorentzMobius_Defs
-- name    : CelestialHolography_LorentzMobius_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T01:41:41.648607+00:00
-- url     : https://prove2.me/theorems/b75e25a9-0a97-4747-98f0-341efc89fa58
-- title:
--   Celestial sphere kinematics: $q^\mu(z)$, $SL(2,\mathbb C)\to$ Lorentz, Möbius maps
-- statement:
--   Definitions for the mission, following §2.2 (eq. (3)) and §3.1 (eq. (11)) of the source.
--
--   * **Minkowski form.** For $x=(x^0,x^1,x^2,x^3)\in\mathbb R^4$, $\;\|x\|^2_\eta = -(x^0)^2+(x^1)^2+(x^2)^2+(x^3)^2$ (mostly-plus signature, as in the Bondi–Sachs metric of the source).
--   * **Celestial null vector (eq. (11)).** For $z\in\mathbb C$,
--   $$q(z)=\tfrac1{\sqrt2}\bigl(1+|z|^2,\;z+\bar z,\;-i(z-\bar z),\;1-|z|^2\bigr)=\tfrac1{\sqrt2}\bigl(1+|z|^2,\;2\,\mathrm{Re}\,z,\;2\,\mathrm{Im}\,z,\;1-|z|^2\bigr).$$
--   * **Hermitian-matrix picture.** $\;H(x)=\begin{pmatrix}x^0-x^3 & x^1+ix^2\\ x^1-ix^2 & x^0+x^3\end{pmatrix}$, so $\det H(x)=-\|x\|^2_\eta$; and the read-off map $V(X)=\bigl(\tfrac{\mathrm{Re}X_{00}+\mathrm{Re}X_{11}}2,\ \mathrm{Re}X_{01},\ \mathrm{Im}X_{01},\ \tfrac{\mathrm{Re}X_{11}-\mathrm{Re}X_{00}}2\bigr)$, which inverts $H$ on Hermitian matrices.
--   * **Lorentz map of $M\in SL(2,\mathbb C)$.** $\Lambda(M)\,x = V\bigl(M\,H(x)\,M^\dagger\bigr)$.
--   * **Möbius map (eq. (3)).** For $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in SL(2,\mathbb C)$, $\;M\cdot z=\dfrac{az+b}{cz+d}$ (with the convention $w/0=0$ at the pole $cz+d=0$).
--
--   The convention for $H$ is chosen so that $H(q(z))=\sqrt2\,(z,1)^{\mathsf T}\overline{(z,1)}$, which makes $\Lambda(M)$ act on $q(z)$ exactly through the Möbius map $z\mapsto (az+b)/(cz+d)$ of eq. (3).
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568, §2.2 eq. (3), §3.1 eq. (11)

import Mathlib

namespace CelestialHolography

/-- The Minkowski quadratic form `-(x⁰)² + (x¹)² + (x²)² + (x³)²` on `ℝ⁴`
(mostly-plus signature). -/
def minkowskiNormSq (x : Fin 4 → ℝ) : ℝ :=
  -(x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2

/-- The null vector `q^μ(z, z̄) = (1/√2)(1 + z z̄, z + z̄, -i(z - z̄), 1 - z z̄)` of eq. (11),
written with real components `z + z̄ = 2 Re z` and `-i(z - z̄) = 2 Im z`. -/
noncomputable def nullVector (z : ℂ) : Fin 4 → ℝ :=
  ![(1 + Complex.normSq z) / Real.sqrt 2, 2 * z.re / Real.sqrt 2,
    2 * z.im / Real.sqrt 2, (1 - Complex.normSq z) / Real.sqrt 2]

/-- The Hermitian `2 × 2` matrix attached to a four-vector:
`x ↦ [[x⁰ - x³, x¹ + i x²], [x¹ - i x², x⁰ + x³]]`. Its determinant is `-minkowskiNormSq x`. -/
noncomputable def toHermitian (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 - x 3 : ℝ), (x 1 : ℂ) + (x 2 : ℂ) * Complex.I;
     (x 1 : ℂ) - (x 2 : ℂ) * Complex.I, (x 0 + x 3 : ℝ)]

/-- Read off a four-vector from a `2 × 2` complex matrix (inverse of `toHermitian`
on Hermitian matrices). -/
noncomputable def fromHermitian (X : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((X 0 0).re + (X 1 1).re) / 2, (X 0 1).re, (X 0 1).im, ((X 1 1).re - (X 0 0).re) / 2]

/-- The linear map of `ℝ⁴` induced by `M ∈ SL(2, ℂ)`: `X ↦ M X M†` on Hermitian matrices. -/
noncomputable def lorentzOfSL2C (M : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fromHermitian ((M : Matrix (Fin 2) (Fin 2) ℂ) * toHermitian x *
    Matrix.conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ))

/-- The Möbius transformation `z ↦ (a z + b) / (c z + d)` of eq. (3), for
`M = [[a, b], [c, d]] ∈ SL(2, ℂ)` (Lean's `x / 0 = 0` convention at the pole). -/
noncomputable def mobius (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)

end CelestialHolography


