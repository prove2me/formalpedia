-- Prove2me | Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem
-- name    : NicaiseDelayWave_InternalStab_InternalDampingProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T19:54:52.607502+00:00
-- url     : https://prove2.me/theorems/6f326920-0451-4000-b792-be4e89cb203b
-- title:
--   Wave equation with delayed internal damping: hypotheses (1.6)–(1.7), (1.17)–(1.18), solutions and the energy 𝓕 (1.19)
-- statement:
--   On a mixed domain $(\Omega,\Gamma_D,\Gamma_N)$ with outer normal $\nu$ this file defines the objects of the internal-feedback problem of Nicaise and Pignotti.
--
--   1. **Convex multiplier** (1.6)–(1.7): $v\in C^2$ and $\alpha>0$ with $\langle D^2v(x)\xi,\xi\rangle\ge2\alpha|\xi|^2$ for all $x\in\overline\Omega$, $\xi\in\mathbb{R}^n$, and $\nabla v(x)\cdot\nu(x)\le0$ for all $x\in\Gamma_D$.
--   2. **Neighbourhood of $\Gamma_N$ in $\Omega$**: an open set $\omega\subset\Omega$ containing $O\cap\Omega$ for some open $O\supset\Gamma_N$.
--   3. **Damping coefficient**: $a\in L^\infty(\Omega)$ (measurable and essentially bounded on $\Omega$) with $a(x)\ge0$ a.e. in $\Omega$ (1.17).
--   4. **Regular solution** of (1.12)–(1.14): $u\in C^2(\mathbb{R}^n\times\mathbb{R})$ such that for every $t>0$
--   $$u_{tt}(x,t)-\Delta u(x,t)+a(x)\big[\mu_1u_t(x,t)+\mu_2u_t(x,t-\tau)\big]=0\quad\text{for a.e. }x\in\Omega,$$
--   $u(x,t)=0$ on $\Gamma_D$ and $\partial u/\partial\nu(x,t)=0$ on $\Gamma_N$. The initial data $u_0=u(\cdot,0)$, $u_1=u_t(\cdot,0)$ (1.15) and the history $g_0=u_t$ on $\Omega\times(-\tau,0)$ (1.16) are the values of $u$ at non-positive times.
--   5. **Free solution** of (4.7)–(4.9): $w\in C^2(\mathbb{R}^n\times\mathbb{R})$ with $w_{tt}-\Delta w=0$ in $\Omega$, $w=0$ on $\Gamma_D$, $\partial w/\partial\nu=0$ on $\Gamma_N$ for $t>0$.
--   6. The **energy** (1.19),
--   $$\mathcal{F}(t)=\frac12\int_\Omega\big\{u_t^2(x,t)+|\nabla u(x,t)|^2\big\}dx+\frac\xi2\int_\Omega a(x)\int_0^1u_t^2(x,t-\tau\rho)\,d\rho\,dx ,$$
--   and the **dissipation** $\int_\Omega a(x)\{u_t^2(x,t)+u_t^2(x,t-\tau)\}dx$ of (4.1) and (4.26).
--
--   These are the objects about which the exponential stability theorem and its milestones are stated.
--
--   **Formalization Note** Solutions are classical ($C^2$ on $\mathbb{R}^n\times\mathbb{R}$); since $a$ is only $L^\infty$ the equation is imposed almost everywhere in $x$. This is a subclass of the paper's regular solutions (whose data need only lie in the domain of the generator), so statements quantified over it are consequences of the paper's. Measurability and essential boundedness of $a$ make every $a$-weighted integral a genuine Lebesgue integral.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1562, (1.6)–(1.7); p. 1563, (1.12)–(1.19); p. 1575, (4.7)–(4.10)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_WaveCalculus

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

variable {n : ℕ}

/-- The geometric hypothesis (1.6)–(1.7) of Nicaise–Pignotti (p. 1562): `v` is `C²`, strictly
convex on `closure Ω` with modulus `α > 0`, i.e. `⟨D²v(x)ξ, ξ⟩ ≥ 2α|ξ|²`, and `H = ∇v`
satisfies `H(x) · ν(x) ≤ 0` on `Γ_D`. -/
def ConvexMultiplier (D : NicaiseDelayWave.Shared.MixedDomain n) (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) : Prop :=
  ContDiff ℝ 2 v ∧ 0 < α ∧
    (∀ x ∈ closure D.Ω, ∀ ξ : EuclideanSpace ℝ (Fin n),
      2 * α * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ v) x ξ ξ) ∧
    ∀ x ∈ D.ΓD, inner ℝ (gradient v x) (D.ν x) ≤ 0

/-- `ω ⊂ Ω` is an open neighbourhood of `Γ_N` inside `Ω`: `ω` is open, `ω ⊆ Ω`, and
`ω ⊇ O ∩ Ω` for some open set `O ⊇ Γ_N`. -/
def IsInteriorNbhdΓN (D : NicaiseDelayWave.Shared.MixedDomain n) (ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsOpen ω ∧ ω ⊆ D.Ω ∧ ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ D.ΓN ⊆ O ∧ O ∩ D.Ω ⊆ ω

/-- The damping coefficient: `a ∈ L^∞(Ω)` (measurable and essentially bounded on `Ω`) with
`a(x) ≥ 0` a.e. in `Ω` (1.17). -/
def IsDampingCoefficient (D : NicaiseDelayWave.Shared.MixedDomain n) (a : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable a ∧ (∃ M : ℝ, ∀ᵐ x ∂(volume.restrict D.Ω), |a x| ≤ M) ∧
    ∀ᵐ x ∂(volume.restrict D.Ω), 0 ≤ a x

/-- A regular (classical) solution of the internally damped wave equation with delay
(1.12)–(1.14): `u` is `C²` on `ℝⁿ × ℝ` and, for every `t > 0`,
`u_tt − Δu + a(x)[μ₁ u_t(x, t) + μ₂ u_t(x, t − τ)] = 0` for a.e. `x ∈ Ω`,
`u = 0` on `Γ_D`, `∂u/∂ν = 0` on `Γ_N`. The initial data (1.15) and the history (1.16) are the
values of `u` and `u_t` for `t ≤ 0`. -/
structure IsRegularSolution (D : NicaiseDelayWave.Shared.MixedDomain n) (a : EuclideanSpace ℝ (Fin n) → ℝ)
    (μ1 μ2 τ : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1 p.2)
  wave_eq : ∀ t > 0, ∀ᵐ x ∂(volume.restrict D.Ω),
    utt u x t - laplacianX u x t + a x * (μ1 * ut u x t + μ2 * ut u x (t - τ)) = 0
  dirichlet : ∀ x ∈ D.ΓD, ∀ t > 0, u x t = 0
  neumann : ∀ x ∈ D.ΓN, ∀ t > 0, normalDeriv D u x t = 0

/-- A regular (classical) solution of the undamped wave equation with mixed boundary conditions
(4.7)–(4.9): `w` is `C²` on `ℝⁿ × ℝ` and, for every `t > 0`, `w_tt − Δw = 0` in `Ω`, `w = 0` on
`Γ_D`, `∂w/∂ν = 0` on `Γ_N`. The initial data (4.10) are `w(·, 0)`, `w_t(·, 0)`. -/
structure IsFreeSolution (D : NicaiseDelayWave.Shared.MixedDomain n) (w : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => w p.1 p.2)
  wave_eq : ∀ x ∈ D.Ω, ∀ t > 0, utt w x t - laplacianX w x t = 0
  dirichlet : ∀ x ∈ D.ΓD, ∀ t > 0, w x t = 0
  neumann : ∀ x ∈ D.ΓN, ∀ t > 0, normalDeriv D w x t = 0

/-- The energy (1.19):
`𝓕(t) = ½ ∫_Ω {u_t² + |∇u|²} dx + (ξ/2) ∫_Ω a(x) ∫₀¹ u_t²(x, t − τρ) dρ dx`. -/
noncomputable def energyF (D : NicaiseDelayWave.Shared.MixedDomain n) (a : EuclideanSpace ℝ (Fin n) → ℝ) (ξ τ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (t : ℝ) : ℝ :=
  stdEnergy D u t + (ξ / 2) * ∫ x in D.Ω, a x * ∫ ρ in (0 : ℝ)..1, ut u x (t - τ * ρ) ^ 2

/-- The dissipation `∫_Ω a(x){u_t²(x, t) + u_t²(x, t − τ)} dx` appearing in (4.1) and (4.26). -/
noncomputable def internalDissipation (D : NicaiseDelayWave.Shared.MixedDomain n) (a : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in D.Ω, a x * (ut u x t ^ 2 + ut u x (t - τ) ^ 2)

end NicaiseDelayWave.InternalStab


