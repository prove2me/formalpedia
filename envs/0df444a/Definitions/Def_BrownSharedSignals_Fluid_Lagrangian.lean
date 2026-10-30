-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_Lagrangian
-- name    : BrownSharedSignals_Fluid_Lagrangian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:47:40.963617+00:00
-- url     : https://prove2.me/theorems/9fc41eaf-4303-43da-95c3-eb15e640b919
-- title:
--   History-dependent Lagrangian values and LP (6)
-- statement:
--   A multiplier schedule assigns a nonnegative real number to each period and complete signal history. The joint Lagrangian value is the Bellman maximum over Cartesian admissible actions, with instantaneous reward equal to the total reward plus the multiplier times unused resources. Resource feasibility is removed. Project Lagrangian values are separate Bellman recursions with local reward minus multiplier times local consumption. Expected future multiplier-budget payments are computed along the exogenous signal chain. All terminal values are zero.
--
--   The optimal relaxation is the infimum over all nonnegative multiplier schedules, not merely schedules depending on the current signal or period. LP (6) has independent project-value coordinates, the Bellman inequalities for every local state/action, nonnegative multipliers, and zero terminal coordinates. Its objective is expected multiplier-budget payments plus the initial project coordinates. Feasibility, optimality and value are defined directly from these constraints. Arbitrary optimal coordinates are not identified with canonical Bellman values at unsupported states. A further recursion evaluates actual policy rewards including Lagrangian penalties.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), §3.1, equations (3)–(6), printed 10–12 / PDF 11–13

import Definitions.Def_BrownSharedSignals_Fluid_StochasticValues

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid
variable {N T : ℕ}
abbrev Multiplier (M : Model N T) := (t : ℕ) → History M t → ℝ

def NonnegativeMultiplier (M : Model N T) (lam : Multiplier M) : Prop :=
  ∀ t < T, ∀ h, 0 ≤ lam t h

def lagrangianAux (M : Model N T) (lam : Multiplier M) :
    (k t : ℕ) → History M t → State M → ℝ
  | 0, _, _, _ => 0
  | k+1, t, h, s => sSup (Set.range fun a : Actions M t s (current M h) =>
      reward M t s (current M h) (actionVector M a) +
      lam t h * (M.budget t (current M h) - consumption M t s (current M h) (actionVector M a)) +
      nextExpectation M t h s (actionVector M a) (lagrangianAux M lam k (t+1)))

def lagrangian (M : Model N T) (lam : Multiplier M) (t : ℕ) (h : History M t) (s : State M) : ℝ :=
  lagrangianAux M lam (T-t) t h s

def projectAux (M : Model N T) (lam : Multiplier M) (i : Fin N) :
    (k t : ℕ) → History M t → Fin (M.stateSize i + 1) → ℝ
  | 0, _, _, _ => 0
  | k+1, t, h, s => sSup (Set.range fun a : Action M t i s (current M h) =>
      (M.project i).reward t s (current M h) a.val - lam t h * M.consumption t i s (current M h) a.val +
      ∑ z', ∑ s', M.signal t (current M h) z' *
        (M.project i).transition t s (current M h) a.val s' * projectAux M lam i k (t+1) (Fin.snoc h z') s')

def projectValue (M : Model N T) (lam : Multiplier M) (t : ℕ) (h : History M t)
    (i : Fin N) (s : Fin (M.stateSize i + 1)) : ℝ := projectAux M lam i (T-t) t h s

def penaltyAux (M : Model N T) (lam : Multiplier M) : (k t : ℕ) → History M t → ℝ
  | 0, _, _ => 0
  | k+1, t, h => lam t h * M.budget t (current M h) +
      ∑ z', M.signal t (current M h) z' * penaltyAux M lam k (t+1) (Fin.snoc h z')

def penalty (M : Model N T) (lam : Multiplier M) (t : ℕ) (h : History M t) : ℝ :=
  penaltyAux M lam (T-t) t h

/-- The optimum over all nonnegative history-dependent multipliers. For a finite model
this is a nonempty, bounded-below infimum; attainment is a theorem target, not a field. -/
def optimalRelaxation (M : Model N T) : ℝ :=
  sInf {v | ∃ lam : Multiplier M, NonnegativeMultiplier M lam ∧
    v = lagrangian M lam 0 (initialHistory M) M.initialState}

def OptimalMultiplier (M : Model N T) (lam : Multiplier M) : Prop :=
  NonnegativeMultiplier M lam ∧ lagrangian M lam 0 (initialHistory M) M.initialState = optimalRelaxation M

abbrev ProjectCoordinates (M : Model N T) :=
  (t : ℕ) → History M t → (i : Fin N) → Fin (M.stateSize i + 1) → ℝ

def localActionValue (M : Model N T) (lam : Multiplier M) (ℓ : ProjectCoordinates M)
    (t : ℕ) (h : History M t) (i : Fin N) (s : Fin (M.stateSize i+1))
    (a : Action M t i s (current M h)) : ℝ :=
  (M.project i).reward t s (current M h) a.val - lam t h * M.consumption t i s (current M h) a.val +
  ∑ z', ∑ s', M.signal t (current M h) z' *
    (M.project i).transition t s (current M h) a.val s' * ℓ (t+1) (Fin.snoc h z') i s'

/-- LP (6): genuine Bellman inequalities; arbitrary optimal coordinates are not
identified by definition with project Bellman values. -/
def LP6Feasible (M : Model N T) (lam : Multiplier M) (ℓ : ProjectCoordinates M) : Prop :=
  NonnegativeMultiplier M lam ∧ (∀ h i s, ℓ T h i s = 0) ∧
  ∀ t < T, ∀ h i s a, localActionValue M lam ℓ t h i s a ≤ ℓ t h i s

def LP6Objective (M : Model N T) (lam : Multiplier M) (ℓ : ProjectCoordinates M) : ℝ :=
  penalty M lam 0 (initialHistory M) + ∑ i, ℓ 0 (initialHistory M) i (M.initialState i)

def LP6Optimal (M : Model N T) (lam : Multiplier M) (ℓ : ProjectCoordinates M) : Prop :=
  LP6Feasible M lam ℓ ∧ ∀ lam' ℓ', LP6Feasible M lam' ℓ' → LP6Objective M lam ℓ ≤ LP6Objective M lam' ℓ'

def LP6Value (M : Model N T) : ℝ :=
  sInf {v | ∃ lam ℓ, LP6Feasible M lam ℓ ∧ v = LP6Objective M lam ℓ}

/-- Evaluation including actual Lagrangian penalties under a mixed policy. -/
def penalizedPolicyAux (M : Model N T) (lam : Multiplier M) (π : Policy M) :
    (k t : ℕ) → History M t → State M → ℝ
  | 0, _, _, _ => 0
  | k+1, t, h, s => ∑ a, π t h s a *
      (reward M t s (current M h) (actionVector M a) +
       lam t h * (M.budget t (current M h) - consumption M t s (current M h) (actionVector M a)) +
       nextExpectation M t h s (actionVector M a) (penalizedPolicyAux M lam π k (t+1)))

end BrownSharedSignals.Fluid


