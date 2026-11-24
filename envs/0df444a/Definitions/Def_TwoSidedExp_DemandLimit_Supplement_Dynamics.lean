-- Prove2me | Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics
-- name    : TwoSidedExp_DemandLimit_Supplement_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:17:02.50951+00:00
-- url     : https://prove2.me/theorems/3485c07b-6628-43df-9c30-8b42ff02bf43
-- title:
--   Mean-field drift (8) and trajectories on nonnegative times
-- statement:
--   Let Γ and Θ be the finite customer and listing type spaces, and let S be the published mean-field system with listing masses ρ, customer shares φ, consideration probabilities α, utilities v, outside options ϵ and holding factors ν. For arrival rate λ and holding scale τ define
--
--   $$f_\theta(s)=(\rho(\theta)-s(\theta))\tau\nu(\theta)-\lambda\sum_\gamma\phi_\gamma p_\gamma(\theta\mid s).$$
--
--   A trajectory solves ds_t(θ)/dt = f_θ(s_t) on t ≥ 0 and takes values in the published state space 0 ≤ s_t(θ) ≤ ρ(θ). This supplies the dynamical objects needed by Proposition 1, Theorems 1–2 and the Lyapunov statement.
--
--   **Formalization Note** Trajectories are functions of real time with coordinate derivatives within [0,∞), including a right derivative at zero; their values at negative times are immaterial. Choice probabilities and the state space are imported, not redeclared.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 11, (6)–(8)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

/-- The mean-field vector field (8), p. 11; τ(θ) = τν(θ). -/
noncomputable def drift (S : MFSystem Γ Θ) (lam tau : ℝ) (s : Θ → ℝ) : Θ → ℝ :=
  fun θ => (S.ρ θ - s θ) * (tau * S.ν θ) - lam * ∑ γ, S.φ γ * S.choice γ θ s

/-- Solutions on [0,∞), including the right derivative at zero, with values in (6).
No condition is imposed at negative times. -/
def Trajectory (S : MFSystem Γ Θ) (lam tau : ℝ) (s : ℝ → Θ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → S.InS (s t)) ∧
  ∀ θ t, 0 ≤ t → HasDerivWithinAt (fun u => s u θ)
    (drift S lam tau (s t) θ) (Set.Ici 0) t

end TwoSidedExp.DemandLimit.Supplement


