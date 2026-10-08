-- Prove2me | Definitions.Def_spherical_ferromagnet_profile_defs
-- name    : spherical_ferromagnet_profile_defs
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-04T14:10:37.822144+00:00
-- url     : https://prove2.me/theorems/20bd7a70-a0a5-43bd-a4d4-396c2590e03c
-- title:
--   Profile equation and hemispheric class $H_{0,2}$ for spherical ferromagnets
-- statement:
--   Axisymmetric fields on $S^2$ with anisotropy $\kappa$ (Gustafson–Meinert–Melcher).
--
--   - `profileOperator κ h θ` $=h''+\cot\theta\,h'-\frac{\sin 2h}{2\sin^2\theta}-\frac{\kappa}{2}\sin(2h-2\theta)$, the left side of (2.6).
--   - `SolvesProfileEq κ h`: it vanishes for all $\theta\in(0,\pi)$.
--   - `inducedField h`: for $x\ne0$, with $\theta=\arccos(x_3/|x|)$ and $r=\sqrt{x_1^2+x_2^2}$, the vector $(\sin h(\theta)\,x_1/r,\ \sin h(\theta)\,x_2/r,\ \cos h(\theta))$, and $(0,0,\cos h(\theta))$ when $r=0$. On $S^2$ this is the field with profile $h$.
--   - `InducesSmoothMap h`: `inducedField h` is $C^\infty$ on $\mathbb R^3\setminus\{0\}$ (equivalent to smoothness on $S^2$).
--   - `IsH02CriticalProfile κ h`: $h$ is $C^\infty$ on $[0,\pi]$, induces a smooth map, solves (2.6), and $h(0)=0$, $h(\pi)=2\pi$, $h(\pi-\theta)=2\pi-h(\theta)$ on $[0,\pi]$.
--
--   Profiles are functions on $\mathbb R$; only their values on $[0,\pi]$ matter. The paper's $H_{0,2}$ allows piecewise $C^1$ profiles; by its Corollary 2.7 the solutions are the same.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.3), eq. (2.6), Lemma 2.3, Definition 3.1; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM, problems/241-spherical-ferromagnet-profile-uniqueness.md)

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace SphericalFerromagnet

open Real Set
open scoped ContDiff

/-- The left-hand side of the profile equation (2.6) of Gustafson–Meinert–Melcher:
`h'' + cot θ · h' - sin(2h) / (2 sin² θ) - (κ/2) sin(2h - 2θ)`. -/
noncomputable def profileOperator (κ : ℝ) (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv (deriv h) θ + Real.cos θ / Real.sin θ * deriv h θ
    - Real.sin (2 * h θ) / (2 * Real.sin θ ^ 2)
    - κ / 2 * Real.sin (2 * h θ - 2 * θ)

/-- `h` solves the profile equation (2.6) at every polar angle `θ ∈ (0, π)`. -/
def SolvesProfileEq (κ : ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Ioo (0 : ℝ) π, profileOperator κ h θ = 0

/-- The axisymmetric field with profile `h`, `m(θ, φ) = (sin h(θ) cos φ, sin h(θ) sin φ, cos h(θ))`,
extended to `ℝ³ \ {0}` as a function of the direction `x / |x|` only. On the polar axis
(`x₁ = x₂ = 0`) it takes the value `(0, 0, cos h(θ))`. -/
noncomputable def inducedField (h : ℝ → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let ρ := Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)
  let r := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
  let θ := Real.arccos (x 2 / ρ)
  if r = 0 then ![0, 0, Real.cos (h θ)]
  else ![Real.sin (h θ) * (x 0 / r), Real.sin (h θ) * (x 1 / r), Real.cos (h θ)]

/-- The profile `h` induces a smooth map `S² → S²`: equivalently, its degree-zero homogeneous
extension `inducedField h` is `C^∞` on `ℝ³ \ {0}`. -/
def InducesSmoothMap (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (inducedField h) {x : Fin 3 → ℝ | x ≠ 0}

/-- `h` is a smooth hemispheric critical profile of class `H_{0,2}` for the anisotropy `κ`:
smooth on `[0, π]`, inducing a smooth map on the sphere, solving (2.6) on `(0, π)`,
with `h(0) = 0`, `h(π) = 2π` and `h(π - θ) = 2π - h(θ)` on `[0, π]`. -/
def IsH02CriticalProfile (κ : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (Icc 0 π) ∧ InducesSmoothMap h ∧ SolvesProfileEq κ h ∧
    h 0 = 0 ∧ h π = 2 * π ∧ ∀ θ ∈ Icc (0 : ℝ) π, h (π - θ) = 2 * π - h θ

end SphericalFerromagnet


