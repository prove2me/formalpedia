-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_FluidControl
-- name    : BrownSharedSignals_Fluid_FluidControl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:49:57.020989+00:00
-- url     : https://prove2.me/theorems/8a2d2515-3d29-4305-b02f-aa71aca47879
-- title:
--   Continuous fluid states, Bellman control and optimal history schedules
-- statement:
--   A fluid state assigns to each project a nonnegative probability vector on its finite local state space. A control is a nonnegative real state-action array whose action marginal is that fluid state and whose total consumption respects the current budget. Its reward is the reward-weighted mass, and its next fluid state is obtained by multiplying the controlled local masses by the local transition kernels. Only the next exogenous signal is random. The continuous Bellman value is defined over all such real controls, with zero terminal payoff.
--
--   A schedule fixes one control for every signal history. Its fluid memory begins at the initial point masses and evolves by the fluid transition formula; an optimal schedule selects a Bellman-optimal control at every rooted history, including null histories. A dynamic fluid policy draws local actions independently from the control divided by local fluid mass where that mass is positive, and uses arbitrary distribution-valued completions at zero mass. It never resets the fluid memory to the realized project states.
--
--   Supergradients are supporting affine upper bounds over the entire product of simplexes. Piecewise linearity is represented by a finite nonempty minimum of affine functions on that domain. Real suprema outside the simplex are total-function extensions and are not the asserted domain of fluid-value properties.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), §4, equations (9)–(10) and Definition 4.1, printed 17–20 / PDF 18–21

import Definitions.Def_BrownSharedSignals_Fluid_Occupancy

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid
variable {N T : ℕ}

abbrev FluidVector (M : Model N T) := (i : Fin N) → Fin (M.stateSize i+1) → ℝ

def IsFluidState (M : Model N T) (f : FluidVector M) : Prop :=
  (∀ i s, 0 ≤ f i s) ∧ ∀ i, ∑ s, f i s = 1

abbrev Control (M : Model N T) (t : ℕ) (z : Signal M) :=
  (i : Fin N) → (s : Fin (M.stateSize i+1)) → Action M t i s z → ℝ

def ControlFeasible (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M) (u : Control M t z) : Prop :=
  (∀ i s a, 0 ≤ u i s a) ∧ (∀ i s, ∑ a, u i s a = f i s) ∧
  (∑ i, ∑ s, ∑ a, M.consumption t i s z a.val * u i s a) ≤ M.budget t z

def fluidReward (M : Model N T) (t : ℕ) (z : Signal M) (u : Control M t z) : ℝ :=
  ∑ i, ∑ s, ∑ a, (M.project i).reward t s z a.val * u i s a

def fluidNext (M : Model N T) (t : ℕ) (z : Signal M) (u : Control M t z) : FluidVector M :=
  fun i s' => ∑ s, ∑ a, (M.project i).transition t s z a.val s' * u i s a

/-- Continuous-simplex Bellman recursion (9). The supremum is over all real
controls, without discretization. On a probability vector the feasible set is a
nonempty compact polytope; finite-horizon rewards bound the objective. -/
def fluidValueAux (M : Model N T) : ℕ → (t : ℕ) → FluidVector M → Signal M → ℝ
  | 0, _, _, _ => 0
  | k+1, t, f, z => sSup {v | ∃ u : Control M t z, ControlFeasible M t f z u ∧
      v = fluidReward M t z u + ∑ z', M.signal t z z' * fluidValueAux M k (t+1) (fluidNext M t z u) z'}

def fluidValue (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M) : ℝ :=
  fluidValueAux M (T-t) t f z

def fluidActionValue (M : Model N T) (t : ℕ) (z : Signal M) (u : Control M t z) : ℝ :=
  fluidReward M t z u + ∑ z', M.signal t z z' * fluidValue M (t+1) (fluidNext M t z u) z'

def ControlOptimal (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M) (u : Control M t z) : Prop :=
  ControlFeasible M t f z u ∧ ∀ v, ControlFeasible M t f z v → fluidActionValue M t z v ≤ fluidActionValue M t z u

def initialFluid (M : Model N T) : FluidVector M :=
  fun i s => if s = M.initialState i then 1 else 0

/-- A fixed deterministic choice of controls indexed by complete signal histories.
Its fluid memory is computed by (10), never reset from realized project states. -/
abbrev Schedule (M : Model N T) := (t : ℕ) → (h : History M t) → Control M t (current M h)

def scheduleState (M : Model N T) (u : Schedule M) : (t : ℕ) → History M t → FluidVector M
  | 0, _ => initialFluid M
  | t+1, h => fluidNext M t (current M (Fin.init h)) (u t (Fin.init h))

def OptimalSchedule (M : Model N T) (u : Schedule M) : Prop :=
  ∀ t < T, ∀ h, h 0 = M.initialSignal →
    ControlOptimal M t (scheduleState M u t h) (current M h) (u t h)

def scheduleOccupancy (M : Model N T) (u : Schedule M) : Occupancy M :=
  fun t h i s a => historyProb M t h * u t h i s a

/-- Definition 4.1 with arbitrary probability distributions at null local occupancies. -/
def DynamicFluidPolicy (M : Model N T) (u : Schedule M) (p : LocalPolicy M) : Prop :=
  OptimalSchedule M u ∧ ∀ t < T, ∀ h, h 0 = M.initialSignal → ∀ i s,
    0 < scheduleState M u t h i s →
      ∀ a, p t h i s a = u t h i s a / scheduleState M u t h i s

def fluidDot (M : Model N T) (v f : FluidVector M) : ℝ := ∑ i, ∑ s, v i s * f i s

def Supergradient (M : Model N T) (t : ℕ) (z : Signal M) (f θ : FluidVector M) : Prop :=
  ∀ g, IsFluidState M g → fluidValue M t g z ≤ fluidValue M t f z +
    ∑ i, ∑ s, θ i s * (g i s - f i s)

/-- Finite minimum of affine functions on the entire probability-simplex domain. -/
structure AffinePieces (M : Model N T) where
  count : ℕ
  slope : Fin (count+1) → FluidVector M
  intercept : Fin (count+1) → ℝ

def piecesValue (M : Model N T) (K : AffinePieces M) (f : FluidVector M) : ℝ :=
  sInf (Set.range fun k => fluidDot M (K.slope k) f + K.intercept k)

def Represents (M : Model N T) (t : ℕ) (z : Signal M) (K : AffinePieces M) : Prop :=
  ∀ f, IsFluidState M f → fluidValue M t f z = piecesValue M K f

end BrownSharedSignals.Fluid


