-- Prove2me | Definitions.Def_ClayNavierStokes_defs
-- name    : ClayNavierStokes_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T18:33:58.713925+00:00
-- url     : https://prove2.me/theorems/01aecf21-bc23-4ec9-9658-33bc73c99656
-- title:
--   Navier–Stokes (Clay problem) — data conditions and solution notions
-- statement:
--   Definitions for the Navier–Stokes equations on $\mathbb R^n$ following Fefferman's Clay problem description:
--
--   1. the divergence $\operatorname{div} v=\operatorname{tr}Dv$ of a vector field and $1$-periodicity $g(x+e_i)=g(x)$;
--   2. admissible initial velocities: smooth and divergence-free, plus either the decay condition (4) $|\partial^\alpha_x u_0(x)|\le C_{\alpha K}(1+|x|)^{-K}$ or $1$-periodicity (8);
--   3. admissible forces: smooth on $\mathbb R^n\times[0,\infty)$, plus either decay (5) $|\partial^\alpha_x\partial^m_t f|\le C(1+|x|+t)^{-K}$ or spatial periodicity (8) with time decay (9);
--   4. global smooth solutions of (1)–(3) on $\mathbb R^n\times[0,\infty)$ with smoothness (6)/(11), plus finite, uniformly bounded energy (7) on the whole space, or periodic velocity (10) and pressure (errata) on the torus;
--   5. local smooth solutions on $\mathbb R^n\times[0,T)$ with the same side conditions restricted to $[0,T)$.
--
--   These definitions are shared by every theorem of the mission.
--
--   **Formalization Note** Time derivatives are taken within $[0,\infty)$ (resp. $[0,T)$), so they are one-sided at $t=0$. Solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$. The torus is encoded through $1$-periodic functions on $\mathbb R^n$. Adapted from the Formal Conjectures file `NavierStokes.lean`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, pp. 1–2, equations (1)–(11) and errata; adapted from the Formal Conjectures file NavierStokes.lean

import Mathlib

/-!
# Clay Millennium Problem: Navier–Stokes existence and smoothness — definitions

Definitions follow C. L. Fefferman, *Existence and smoothness of the Navier–Stokes
equation* (Clay Mathematics Institute), equations (1)–(11) and the errata, adapted from
the Formal Conjectures file `NavierStokes.lean`. Space is `EuclideanSpace ℝ (Fin n)`;
the velocity is `v x t`, the pressure `p x t`, the force `f x t` (position before time).
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace ClayNavierStokes

variable {n : ℕ}

/-- Divergence `∇ · v` of `v : ℝⁿ → ℝⁿ` at `x`: the trace of the Fréchet derivative
(junk value `0` where `v` is not differentiable). -/
noncomputable def divergence (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (fderiv ℝ v x)

/-- `f` is 1-periodic in each coordinate direction: `f (x + eᵢ) = f x`. -/
def IsOnePeriodic {α : Sort*} (f : EuclideanSpace ℝ (Fin n) → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

/-- Initial velocity: divergence-free (2) and `C^∞`. -/
structure InitialVelocityCondition
    (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  div_free : ∀ x, divergence u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

/-- Initial velocity on `ℝⁿ`: additionally condition (4), rapid decay of all derivatives. -/
structure InitialVelocityConditionDecay
    (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop
    extends InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- Initial velocity on the torus: additionally 1-periodic (8). -/
structure InitialVelocityConditionPeriodic
    (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop
    extends InitialVelocityCondition u₀ where
  isOnePeriodic : IsOnePeriodic u₀

/-- Force: `C^∞` on `ℝⁿ × [0, ∞)`. -/
structure ForceCondition (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) :
    Prop where
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

/-- Force on `ℝⁿ`: additionally condition (5), decay in space and time. -/
structure ForceConditionDecay (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) :
    Prop extends ForceCondition f where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K

/-- Force on the torus: additionally 1-periodic in space (8) and decaying in time (9). -/
structure ForceConditionPeriodic
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) : Prop
    extends ForceCondition f where
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

/-- A global smooth solution `(v, p)` on `ℝⁿ × [0, ∞)`: equations (1), (2), (3) and
smoothness (6)/(11). -/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ≥ 0, divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

/-- Global solution on `ℝⁿ`: additionally square-integrable with bounded energy (7). -/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop
    extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  integrable : ∀ t ≥ 0, MemLp (fun x => ‖v x t‖) 2
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x, ‖v x t‖ ^ 2) < E

/-- Global solution on the torus: additionally velocity (10) and pressure (errata)
1-periodic in space. -/
structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop
    extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)

/-- A smooth solution on the finite time window `ℝⁿ × [0, T)`: equations (1), (2), (3)
for `0 ≤ t < T` (time derivative taken within `[0, T)`) and smoothness on `ℝⁿ × [0, T)`. -/
structure NavierStokesLocalSmoothSolution
    (nu : ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (v : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ∈ Set.Ico 0 T,
    derivWithin (v x ·) (Set.Ico 0 T) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ∈ Set.Ico 0 T, divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ico 0 T)
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ico 0 T)

/-- Local solution on `ℝⁿ`: additionally condition (7) on `[0, T)`. -/
structure NavierStokesLocalSmoothSolutionRn
    (nu : ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (v : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop
    extends NavierStokesLocalSmoothSolution nu u₀ f T v p where
  integrable : ∀ t ∈ Set.Ico 0 T, MemLp (fun x => ‖v x t‖) 2
  bounded_energy : ∃ E, ∀ t ∈ Set.Ico 0 T, (∫ x, ‖v x t‖ ^ 2) < E

/-- Local solution on the torus: additionally (10) and periodic pressure on `[0, T)`. -/
structure NavierStokesLocalSmoothSolutionPeriodic
    (nu : ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (v : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop
    extends NavierStokesLocalSmoothSolution nu u₀ f T v p where
  isOnePeriodic_velocity : ∀ t ∈ Set.Ico 0 T, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ∈ Set.Ico 0 T, IsOnePeriodic (p · t)

end ClayNavierStokes


