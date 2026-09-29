-- Prove2me | Definitions.Def_HilbertSixth_Fluid
-- name    : HilbertSixth_Fluid
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T04:12:42.374274+00:00
-- url     : https://prove2.me/theorems/f8da3333-0c46-4c3f-ba64-dcb2bafc9c46
-- title:
--   Incompressible Navier--Stokes--Fourier, compressible Euler, and well-prepared kinetic data
-- statement:
--   The fluid systems and the kinetic data used in the hydrodynamic half of arXiv:2503.01800.
--
--   The incompressible Navier-Stokes-Fourier system (1.19) on $\mathbb{T}^d$ reads
--
--   $$\partial_t u + (u\cdot\nabla)u - \mu_1 \Delta u = -\nabla p, \qquad \partial_t \rho + (u\cdot\nabla)\rho - \mu_2\Delta\rho = 0, \qquad \operatorname{div} u = 0,$$
--
--   with $u$ and $\rho$ of zero mean on the torus. The compressible Euler system (1.40) reads
--
--   $$\partial_t\rho + \nabla\cdot(\rho u) = 0, \quad \partial_t(\rho u) + \nabla\cdot(\rho u \otimes u) + \nabla p = 0,$$
--   $$\partial_t\Big(\rho\frac{d\Theta + |u|^2}{2}\Big) + \nabla\cdot\Big(\rho u \frac{d\Theta + |u|^2}{2}\Big) + \nabla\cdot(p u) = 0, \qquad p = \rho\,\Theta,$$
--
--   with positive density and temperature. Also formalized: the well-prepared kinetic data (1.21)
--
--   $$n_0(x,v) = \frac{e^{-|v|^2/2}}{(2\pi)^{d/2}}\Big[1 + \delta\Big(\tfrac{2+d-|v|^2}{2}\rho_0(x) + v\cdot u_0(x)\Big) + \delta^4 e^{|v|^2/4} g_R(x,v)\Big],$$
--
--   the fluctuation profile appearing in (1.22) and (1.26), and the weighted derivative bounds used for the perturbations $g_R$ and $F_R$ in (1.20) and (1.44).
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, eq. (1.19), (1.20), (1.21), (1.22), (1.40), (1.44)

import Definitions.Def_HilbertSixth_Boltzmann

/-!
# Fluid equations and well-prepared kinetic data

Formalization of the fluid systems appearing in Deng–Hani–Ma, *Hilbert's sixth
problem: derivation of fluid equations via Boltzmann's kinetic theory*
(arXiv:2503.01800): the incompressible Navier–Stokes–Fourier system (1.19), the
compressible Euler system (1.40), the well-prepared kinetic data (1.21) and the
local-Maxwellian fluctuation profile appearing in (1.22) and (1.26).

All fluid unknowns are functions of `(t, x) ∈ ℝ × ℝ^d`; the torus `T^d` is encoded
by `ℤ^d`-periodicity in `x`, and integrals in `x` are taken over the fundamental
domain `box d = [0,1)^d`.
-/

open MeasureTheory

namespace HilbertSixth

/-- Smoothness and `ℤ^d`-periodicity of a scalar field `(t, x) ↦ f t x`. -/
def SmoothPeriodicScalar (d : ℕ) (f : ℝ → Vec d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => f q.1 q.2) ∧ ∀ t : ℝ, PeriodicPos (f t)

/-- Smoothness and `ℤ^d`-periodicity of a vector field `(t, x) ↦ u t x`. -/
def SmoothPeriodicVector (d : ℕ) (u : ℝ → Vec d → Vec d) : Prop :=
  (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => u q.1 q.2 i)) ∧
    ∀ (t : ℝ) (i : Fin d), PeriodicPos (fun x => u t x i)

/-- **Equation (1.19) — the incompressible Navier–Stokes–Fourier system on `T^d`**
with viscosity `μ₁` and thermal diffusivity `μ₂`:
`∂_t u + (u · ∇) u - μ₁ Δu = -∇p`, `∂_t ρ + (u · ∇) ρ - μ₂ Δρ = 0`, `div u = 0`,
together with the zero-mean normalisation of `u` and `ρ` on the torus, on the time
interval `[0, Tfin]`. -/
def IsNSFSolution (d : ℕ) (μ₁ μ₂ Tfin : ℝ) (u : ℝ → Vec d → Vec d)
    (ρ p : ℝ → Vec d → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ (x : Vec d) (i : Fin d),
      deriv (fun s : ℝ => u s x i) t + advect (u t) (fun y => u t y i) x
        - μ₁ * laplacian (fun y => u t y i) x = -partialD (p t) i x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x : Vec d,
      deriv (fun s : ℝ => ρ s x) t + advect (u t) (ρ t) x
        - μ₂ * laplacian (ρ t) x = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x : Vec d, divergence (u t) x = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∫ x in box d, ρ t x = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ i : Fin d, ∫ x in box d, u t x i = 0)

/-- **Equation (1.40) — the compressible Euler system on `T^d`** for the density `ρ`,
the velocity `u`, the temperature `Θ` and the pressure `p`:
`∂_t ρ + ∇ · (ρ u) = 0`,
`∂_t (ρ u) + ∇ · (ρ u ⊗ u) + ∇ p = 0`,
`∂_t (ρ (dΘ + |u|²)/2) + ∇ · (ρ u (dΘ + |u|²)/2) + ∇ · (p u) = 0`,
`p = ρ Θ`,
on the time interval `[0, Tfin]`, with `ρ` and `Θ` positive. -/
def IsCompressibleEulerSolution (d : ℕ) (Tfin : ℝ) (ρ Θ p : ℝ → Vec d → ℝ)
    (u : ℝ → Vec d → Vec d) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x : Vec d, 0 < ρ t x ∧ 0 < Θ t x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x : Vec d,
      deriv (fun s : ℝ => ρ s x) t + ∑ i, partialD (fun y => ρ t y * u t y i) i x = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ (x : Vec d) (i : Fin d),
      deriv (fun s : ℝ => ρ s x * u s x i) t
        + ∑ j, partialD (fun y => ρ t y * u t y i * u t y j) j x
        + partialD (p t) i x = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x : Vec d,
      deriv (fun s : ℝ => ρ s x * (((d : ℝ) * Θ s x + ‖u s x‖ ^ 2) / 2)) t
        + ∑ i, partialD
            (fun y => ρ t y * u t y i * (((d : ℝ) * Θ t y + ‖u t y‖ ^ 2) / 2)) i x
        + ∑ i, partialD (fun y => p t y * u t y i) i x = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x : Vec d, p t x = ρ t x * Θ t x)

/-- The local-Maxwellian fluctuation profile of (1.22) and (1.26):
`(2π)^{-d/2} e^{-|v|²/2} (1 + δ ((2 + d - |v|²)/2 · ρ(x) + v · u(x)))`. -/
noncomputable def nsfProfile (d : ℕ) (δ : ℝ) (ρ : Vec d → ℝ) (u : Vec d → Vec d)
    (x v : Vec d) : ℝ :=
  globalMaxwellian d v *
    (1 + δ * ((2 + (d : ℝ) - ‖v‖ ^ 2) / 2 * ρ x + dotp v (u x)))

/-- **Equation (1.21) — the well-prepared initial kinetic data** for the
incompressible Navier–Stokes–Fourier limit:
`n₀(x,v) = (2π)^{-d/2} e^{-|v|²/2} [1 + δ ((2 + d - |v|²)/2 · ρ₀(x) + v · u₀(x))
             + δ⁴ e^{|v|²/4} g_R(x,v)]`. -/
noncomputable def nsfInitialData (d : ℕ) (δ : ℝ) (ρ₀ : Vec d → ℝ) (u₀ : Vec d → Vec d)
    (gR : Vec d → Vec d → ℝ) (x v : Vec d) : ℝ :=
  globalMaxwellian d v *
    (1 + δ * ((2 + (d : ℝ) - ‖v‖ ^ 2) / 2 * ρ₀ x + dotp v (u₀ x))
      + δ ^ 4 * Real.exp (‖v‖ ^ 2 / 4) * gR x v)

/-- `WeightedDerivBound d m w F` says that all joint derivatives of `F` in `(x, v)`
of total order at most `m`, weighted by `w`, are bounded by `1` in supremum norm.

Used for the perturbation bounds (1.20) and (1.44), with `m = 4d` and weight
`⟨v⟩^{2d}` (resp. `M^{-1/2} ⟨v⟩^{2d}`); bounding all joint derivatives of total
order `≤ 4d` implies the bound on each mixed derivative `∂_x^μ ∂_v^ν` with
`|μ|, |ν| ≤ 2d` required in the source. -/
def WeightedDerivBound (d m : ℕ) (w : Vec d → Vec d → ℝ) (F : Vec d → Vec d → ℝ) :
    Prop :=
  ∀ k ≤ m, ∀ x v : Vec d,
    w x v * ‖iteratedFDeriv ℝ k (fun z : Vec d × Vec d => F z.1 z.2) (x, v)‖ ≤ 1

end HilbertSixth


