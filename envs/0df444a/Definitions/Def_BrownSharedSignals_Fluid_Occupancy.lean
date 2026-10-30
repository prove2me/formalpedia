-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_Occupancy
-- name    : BrownSharedSignals_Fluid_Occupancy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:48:41.089189+00:00
-- url     : https://prove2.me/theorems/ce6ab645-762d-4d62-a72f-4c7146df7cf9
-- title:
--   The full state-action occupancy LP (7)
-- statement:
--   Occupancy variables are real masses indexed by period, complete signal history, project, local state and admissible action. LP (7) imposes nonnegativity, a budget at each history scaled by that history’s probability, the deterministic initial point mass for every local state and signal, and the full project/signal flow-balance equations. The objective is the sum of rewards times occupancies. Feasible and optimal solutions are defined from these constraints and this objective.
--
--   The associated independent policy normalizes each local occupancy row wherever its mass is positive. At zero mass it permits any genuine probability distribution on the admissible actions. No optimal-action-support condition is built into that completion. Attainment, LP duality and policy optimality are theorem conclusions, not fields of this definition.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), §3.2, equation (7) and Proposition 3.2 setup, printed 15–16 / PDF 16–17

import Definitions.Def_BrownSharedSignals_Fluid_Lagrangian

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid
variable {N T : ℕ}

abbrev Occupancy (M : Model N T) := (t : ℕ) → (h : History M t) →
  (i : Fin N) → (s : Fin (M.stateSize i+1)) → Action M t i s (current M h) → ℝ

def occupancyMass (M : Model N T) (μ : Occupancy M) (t : ℕ) (h : History M t)
    (i : Fin N) (s : Fin (M.stateSize i+1)) : ℝ := ∑ a, μ t h i s a

/-- The full state-action occupancy LP (7), including the initial point mass at
all states/histories, and the history-specific budget and forward equations. -/
def LP7Feasible (M : Model N T) (μ : Occupancy M) : Prop :=
  (∀ t < T, ∀ h i s a, 0 ≤ μ t h i s a) ∧
  (∀ t < T, ∀ h, (∑ i, ∑ s, ∑ a,
    M.consumption t i s (current M h) a.val * μ t h i s a) ≤ historyProb M t h * M.budget t (current M h)) ∧
  (∀ h i s, occupancyMass M μ 0 h i s = if h 0 = M.initialSignal ∧ s = M.initialState i then 1 else 0) ∧
  (∀ t, t+1 < T → ∀ h z' i s',
    occupancyMass M μ (t+1) (Fin.snoc h z') i s' =
      M.signal t (current M h) z' * ∑ s, ∑ a,
        (M.project i).transition t s (current M h) a.val s' * μ t h i s a)

def LP7Objective (M : Model N T) (μ : Occupancy M) : ℝ :=
  ∑ t : Fin T, ∑ h : History M t.val, ∑ i, ∑ s, ∑ a,
    (M.project i).reward t.val s (current M h) a.val * μ t.val h i s a

def LP7Optimal (M : Model N T) (μ : Occupancy M) : Prop :=
  LP7Feasible M μ ∧ ∀ ν, LP7Feasible M ν → LP7Objective M ν ≤ LP7Objective M μ

def LP7Value (M : Model N T) : ℝ :=
  sSup {v | ∃ μ, LP7Feasible M μ ∧ v = LP7Objective M μ}

/-- Independent normalized-occupancy policy with a distribution-valued completion
at zero local mass. No optimal-action support requirement is imposed at zero mass. -/
def OccupancyPolicy (M : Model N T) (μ : Occupancy M) (p : LocalPolicy M) : Prop :=
  ∀ t < T, ∀ h i s, 0 < occupancyMass M μ t h i s →
    ∀ a, p t h i s a = μ t h i s a / occupancyMass M μ t h i s

end BrownSharedSignals.Fluid


