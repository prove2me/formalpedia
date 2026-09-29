-- Prove2me | Definitions.Def_RobustMDP_Stationarity_gameValues
-- name    : RobustMDP_Stationarity_gameValues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:23:30.387134+00:00
-- url     : https://prove2.me/theorems/1eab0a8d-b756-4bd3-840d-c3847694b568
-- title:
--   The six robust game values $\phi_\infty(\cdot,\cdot)$ and $\phi_N(\Pi,\cdot)$
-- statement:
--   In the robust discounted MDP (definition `RobustMDP_Stationarity_Model`), with discount $\nu$ and initial state $i_0$, the controller minimizes the worst-case cost over nature. For controller class $\Pi$ or $\Pi_s$ and nature class $\mathcal T$ or $\mathcal T_s$:
--   $$
--   \phi_\infty(\Pi,\mathcal T)=\inf_{\pi\in\Pi}\sup_{\tau\in\mathcal T}C_\infty(\pi,\tau),\qquad \phi_\infty(\Pi_s,\mathcal T_s)=\inf_{\pi\in\Pi_s}\sup_{\tau\in\mathcal T_s}C_\infty(\pi,\tau)\ \text{(problem (6))},
--   $$
--   and $\phi_\infty(\Pi_s,\mathcal T)$, $\phi_\infty(\Pi,\mathcal T_s)$ likewise. For a horizon $N$,
--   $$
--   \phi_N(\Pi,\mathcal T)=\inf_{\pi\in\Pi}\sup_{\tau\in\mathcal T}C_N(\pi,\tau)\ \text{(problem (4))},\qquad \phi_N(\Pi,\mathcal T_s)=\inf_{\pi\in\Pi}\sup_{\tau\in\mathcal T_s}C_N(\pi,\tau)\ \text{(problem (3))},
--   $$
--   both with the discounted stage costs $\nu^t c$ and zero terminal cost.
--
--   Theorem 4 of Nilim and El Ghaoui states that the four infinite-horizon values coincide and that the two finite-horizon values differ by an amount that vanishes geometrically in $N$.
--
--   **Formalization Note** The paper writes min and max; here they are `⨅` and `⨆` over real numbers. Every family involved is nonempty (the action set and every row set are nonempty) and lies in $[0,c_{\max}/(1-\nu)]$ when $0<\nu<1$, so these are genuine infima and suprema; attainment is not assumed. A stationary nature policy is the constant sequence of one choice `P : M.Choice`, a stationary controller policy the constant sequence of one `Fin n → A`. The finite-horizon values range over infinite sequences, but $C_N$ ignores stages $\ge N$, so they equal the paper's values over $\mathcal A^{nN}$ and $(\otimes_a\mathcal P^a)^N$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 781 (Eq. (3)), p. 782 (Eqs. (4), (6) and the sentence defining φ_∞(Π, 𝒯), φ_∞(Π, 𝒯_s), φ_∞(Π_s, 𝒯))

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model

namespace RobustMDP.Stationarity

variable {n : ℕ} {A : Type} (M : Model n A) (ν : ℝ) (i₀ : Fin n)

/-- `φ_∞(Π, 𝒯) = inf_{π ∈ Π} sup_{τ ∈ 𝒯} C_∞(π, τ)`: time-varying controller and nature. -/
noncomputable def Model.phiInf_PT : ℝ :=
  ⨅ π : Policy n A, ⨆ τ : M.NaturePolicy, M.infCost ν i₀ π τ

/-- `φ_∞(Π_s, 𝒯_s) = inf_{π ∈ Π_s} sup_{τ ∈ 𝒯_s} C_∞(π, τ)`, problem (6): stationary controller and
stationary nature. -/
noncomputable def Model.phiInf_PsTs : ℝ :=
  ⨅ π : Fin n → A, ⨆ P : M.Choice, M.infCost ν i₀ (fun _ => π) (fun _ => P)

/-- `φ_∞(Π_s, 𝒯) = inf_{π ∈ Π_s} sup_{τ ∈ 𝒯} C_∞(π, τ)`: stationary controller, time-varying
nature. -/
noncomputable def Model.phiInf_PsT : ℝ :=
  ⨅ π : Fin n → A, ⨆ τ : M.NaturePolicy, M.infCost ν i₀ (fun _ => π) τ

/-- `φ_∞(Π, 𝒯_s) = inf_{π ∈ Π} sup_{τ ∈ 𝒯_s} C_∞(π, τ)`: time-varying controller, stationary
nature. -/
noncomputable def Model.phiInf_PTs : ℝ :=
  ⨅ π : Policy n A, ⨆ P : M.Choice, M.infCost ν i₀ π (fun _ => P)

/-- `φ_N(Π, 𝒯) = inf_{π ∈ Π} sup_{τ ∈ 𝒯} C_N(π, τ)`, problem (4) with the discounted cost function.
`C_N` reads only the first `N` stages of `π` and `τ`. -/
noncomputable def Model.phiN_PT (N : ℕ) : ℝ :=
  ⨅ π : Policy n A, ⨆ τ : M.NaturePolicy, M.finiteCost ν i₀ N π τ

/-- `φ_N(Π, 𝒯_s) = inf_{π ∈ Π} sup_{τ ∈ 𝒯_s} C_N(π, τ)`, problem (3) with the discounted cost
function. -/
noncomputable def Model.phiN_PTs (N : ℕ) : ℝ :=
  ⨅ π : Policy n A, ⨆ P : M.Choice, M.finiteCost ν i₀ N π (fun _ => P)

end RobustMDP.Stationarity


