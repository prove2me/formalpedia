-- Prove2me | Definitions.Def_DynSetValue_DPP_Game
-- name    : DynSetValue_DPP_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:18.941801+00:00
-- url     : https://prove2.me/theorems/69bc15e3-d587-4842-80a7-dbbf91925812
-- title:
--   Girsanov costs and approximate Nash equilibria
-- statement:
--   A profile $\alpha$ consists of one progressively measurable, action-valued process per player; each unilateral deviation ranges over all such processes. At a history $(t,\omega)$, only the game coefficients and terminal payoff are shifted by concatenation, while the control is evaluated at the elapsed time $s$. A coordinatewise Itô integral defines the Girsanov density
--
--   $$
--   M^{t,\omega,\alpha}_{T-t}=\exp\!\left(\int_0^{T-t}b^{t,\omega}(s,B,\alpha_s)\cdot dB_s-
--   \frac12\int_0^{T-t}|b^{t,\omega}(s,B,\alpha_s)|^2ds\right).
--   $$
--
--   The vector cost $J(t,\omega,\alpha)$ is the expectation of shifted terminal plus running cost under this density. The stopped cost $J(\tau,\eta;t,\omega,\alpha)$ replaces the terminal cost by $\eta$ and stops the running integral at $\tau^{t,\omega}-t$. The predicates $NE_\varepsilon$ and $NE_\varepsilon^{\rm stop}$ demand that no admissible unilateral deviation improves a player's cost by more than $\varepsilon$.
--
--   These definitions provide the stochastic-game interface for the set-value principle.
--
--   **Formalization Note** The Itô integrals are selected from the published Ethier–Kurtz step-approximation relation. Their existence and payoff integrability under Assumption 3.1 are proof obligations, rather than independent assumptions on the goal.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 22, equation (3.2), Definition 3.3; p. 28, equation (3.9)

import Mathlib
import Definitions.Def_DynSetValue_DPP_Setting
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

variable {T : ℝ} (hT : 0 < T) {d N : ℕ}

abbrev Profile (G : Game T hT d N) :=
  (i : Fin N) → Interval T → Ω T d → State (G.actions.m i)

/-- Every component is a progressively measurable, action-valued process. -/
def IsControl (G : Game T hT d N) (P0 : Measure (Ω T d))
    (i : Fin N) (α : Interval T → Ω T d → State (G.actions.m i)) : Prop :=
  IsStronglyProgressive (𝓕Interval hT P0) α ∧
  ∀ s ω, α s ω ∈ G.actions.A i

def IsProfile (G : Game T hT d N) (P0 : Measure (Ω T d)) (α : Profile hT G) : Prop :=
  ∀ i, IsControl hT G P0 i (α i)

/-- Replace just player i's control. -/
def deviate (G : Game T hT d N) (α : Profile hT G) (i : Fin N)
    (β : Interval T → Ω T d → State (G.actions.m i)) : Profile hT G :=
  fun j => if h : j = i then h.symm ▸ β else α j

/-- Drift after fixing the path history (t,ω). The control is not shifted. -/
noncomputable def bShift (G : Game T hT d N) (t : ℝ) (ω : Ω T d)
    (α : Profile hT G) (s : ℝ) (ω' : Ω T d) : State d :=
  G.b (t + s) (concat hT t ω ω') (fun i => α i (clamp T hT s) ω')

noncomputable def fShift (G : Game T hT d N) (i : Fin N) (t : ℝ)
    (ω : Ω T d) (α : Profile hT G) (s : ℝ) (ω' : Ω T d) : ℝ :=
  G.f i (t + s) (concat hT t ω ω') (α i (clamp T hT s) ω')

noncomputable def ξShift (G : Game T hT d N) (t : ℝ)
    (ω ω' : Ω T d) : Payoff N := G.ξ (concat hT t ω ω')

/-- One candidate collection of the d coordinate Itô integrals. -/
def IsItoChoice (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (α : Profile hT G)
    (Z : Fin d → ℝ≥0 → Ω T d → ℝ) : Prop :=
  ∀ k : Fin d,
    EthierKurtz.HasBrownianItoIntegral P0 (fun s => 𝓕 hT P0 (s : ℝ))
      (fun s ω' => B hT (s : ℝ) ω' k)
      (fun s ω' => if (s : ℝ) ≤ T - t then
        bShift hT G t ω α (s : ℝ) ω' k else 0)
      (Z k)

/-- Classical selection of the stochastic integral, which is unique almost surely
whenever the bounded progressive integrand admits the standard construction. -/
noncomputable def itoChoice (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (α : Profile hT G) :
    Fin d → ℝ≥0 → Ω T d → ℝ :=
  Classical.epsilon (IsItoChoice hT G P0 t ω α)

noncomputable def itoSum (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (α : Profile hT G) (ω' : Ω T d) : ℝ :=
  ∑ k : Fin d, itoChoice hT G P0 t ω α k (Real.toNNReal (T - t)) ω'

/-- Formula (3.2): the Girsanov density on the shifted horizon. -/
noncomputable def M (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (α : Profile hT G) (ω' : Ω T d) : ℝ :=
  Real.exp (itoSum hT G P0 t ω α ω' -
    (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..(T - t), ‖bShift hT G t ω α s ω'‖ ^ 2)

/-- Formula (3.5), equivalent to expectation under the changed measure in (3.2). -/
noncomputable def J (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (α : Profile hT G) : Payoff N :=
  WithLp.toLp 2 (fun i : Fin N =>
    ∫ ω' : Ω T d, M hT G P0 t ω α ω' *
      ((ξShift hT G t ω ω') i +
        ∫ s in (0 : ℝ)..(T - t), fShift hT G i t ω α s ω') ∂P0)

/-- A total real representative of a bounded stopping time. -/
noncomputable def stopTime (τ : Ω T d → WithTop ℝ) (ω : Ω T d) : ℝ :=
  (τ ω).untopD T

/-- The stopped cost (3.9). The density still runs to T−t. -/
noncomputable def Jstop (G : Game T hT d N) (P0 : Measure (Ω T d))
    (τ : Ω T d → WithTop ℝ) (η : Ω T d → Payoff N)
    (t : ℝ) (ω : Ω T d) (α : Profile hT G) : Payoff N :=
  WithLp.toLp 2 (fun i : Fin N =>
    ∫ ω' : Ω T d, M hT G P0 t ω α ω' *
      ((η (concat hT t ω ω')) i +
        ∫ s in Set.Ioc (0 : ℝ) (stopTime τ (concat hT t ω ω') - t),
          fShift hT G i t ω α s ω' ∂volume) ∂P0)

/-- Definition 3.3, with deviations over all admissible controls. -/
def NEε (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (ε : ℝ) (α : Profile hT G) : Prop :=
  IsProfile hT G P0 α ∧
  ∀ i (β : Interval T → Ω T d → State (G.actions.m i)),
    IsControl hT G P0 i β →
      J hT G P0 t ω α i ≤ J hT G P0 t ω (deviate hT G α i β) i + ε

/-- The analogous equilibrium of the game stopped at τ with terminal η. -/
def NEεStop (G : Game T hT d N) (P0 : Measure (Ω T d))
    (τ : Ω T d → WithTop ℝ) (η : Ω T d → Payoff N)
    (t : ℝ) (ω : Ω T d) (ε : ℝ) (α : Profile hT G) : Prop :=
  IsProfile hT G P0 α ∧
  ∀ i (β : Interval T → Ω T d → State (G.actions.m i)),
    IsControl hT G P0 i β →
      Jstop hT G P0 τ η t ω α i ≤
        Jstop hT G P0 τ η t ω (deviate hT G α i β) i + ε

end DynSetValue.DPP


