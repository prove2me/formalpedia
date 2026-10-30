-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_Model
-- name    : BrownSharedSignals_Fluid_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:46:12.160659+00:00
-- url     : https://prove2.me/theorems/ff230109-a840-40f9-a263-279d0808c1fc
-- title:
--   Shared-resource projects and exogenous signals
-- statement:
--   A model consists of N finite nonempty project state spaces, a finite nonempty signal space, a positive finite horizon T, one controlled Markov process for each project, and a normalized exogenous signal kernel. Local action sets can differ with time, state, signal and project. Rewards are real, including negative rewards. Resource use is zero at the zero action and strictly positive at every nonzero admissible action. Budgets are nonnegative. Initial states and the initial signal are deterministic.
--
--   The joint transition probability is the signal transition probability multiplied by the product of project transition probabilities. Cartesian admissibility and resource feasibility are separate: a joint action is feasible precisely when its total consumption does not exceed the current budget. Histories include every signal observed so far. Their probability includes the deterministic initial signal. A separate boundedness predicate records signed reward bounds and positive lower and upper consumption scales only during actual decision periods and at admissible actions.
--
--   Finite carriers use numbered types of size at least one; period 0 represents source period 1, and T is terminal. Data outside the finite horizon are harmless extensions; no theorem uses their rewards as actual payoffs.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), §2 and §6, printed 5–7,25–26 / PDF 6–8,26–27

import Definitions.Def_BrownSharedSignals_Fluid_ControlledProcess

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid

/-- §2. Finite nonempty carriers are numbered by `Fin (size + 1)`.
Period `t = 0` is the source's period 1; `T` is terminal. -/
structure Model (N T : ℕ) where
  horizon_pos : 0 < T
  stateSize : Fin N → ℕ
  signalSize : ℕ
  project : (i : Fin N) → ControlledProcess (Fin (stateSize i + 1)) (Fin (signalSize + 1))
  signal : ℕ → Fin (signalSize + 1) → Arlib.Probability.FinDist (Fin (signalSize + 1))
  consumption : (t : ℕ) → (i : Fin N) → Fin (stateSize i + 1) → Fin (signalSize + 1) → ℝ → ℝ
  consumption_zero : ∀ t i s z, consumption t i s z 0 = 0
  consumption_pos : ∀ t i s z a, a ∈ (project i).actions t s z → a ≠ 0 → 0 < consumption t i s z a
  budget : ℕ → Fin (signalSize + 1) → ℝ
  budget_nonneg : ∀ t z, 0 ≤ budget t z
  initialState : (i : Fin N) → Fin (stateSize i + 1)
  initialSignal : Fin (signalSize + 1)

variable {N T : ℕ}
abbrev State (M : Model N T) := (i : Fin N) → Fin (M.stateSize i + 1)
abbrev Signal (M : Model N T) := Fin (M.signalSize + 1)
abbrev History (M : Model N T) (t : ℕ) := Fin (t + 1) → Signal M
abbrev current (M : Model N T) {t : ℕ} (h : History M t) := h (Fin.last t)
abbrev Action (M : Model N T) (t : ℕ) (i : Fin N) (s : Fin (M.stateSize i + 1)) (z : Signal M) :=
  {a : ℝ // a ∈ (M.project i).actions t s z}
abbrev Actions (M : Model N T) (t : ℕ) (s : State M) (z : Signal M) :=
  (i : Fin N) → Action M t i (s i) z

instance actionFintype (M : Model N T) (t : ℕ) (i : Fin N)
    (s : Fin (M.stateSize i + 1)) (z : Signal M) : Fintype (Action M t i s z) :=
  Finset.fintypeCoeSort ((M.project i).actions t s z)

abbrev actionVector (M : Model N T) {t : ℕ} {s : State M} {z : Signal M}
    (a : Actions M t s z) : Fin N → ℝ := fun i => (a i).val

def reward (M : Model N T) (t : ℕ) (s : State M) (z : Signal M) (a : Fin N → ℝ) : ℝ :=
  ∑ i, (M.project i).reward t (s i) z (a i)
def consumption (M : Model N T) (t : ℕ) (s : State M) (z : Signal M) (a : Fin N → ℝ) : ℝ :=
  ∑ i, M.consumption t i (s i) z (a i)
def FeasibleAction (M : Model N T) (t : ℕ) (s : State M) (z : Signal M) (a : Actions M t s z) : Prop :=
  consumption M t s z (actionVector M a) ≤ M.budget t z

/-- The actual one-step law: the exogenous signal law times the local product. -/
def transition (M : Model N T) (t : ℕ) (s : State M) (z : Signal M)
    (a : Fin N → ℝ) (s' : State M) (z' : Signal M) : ℝ :=
  M.signal t z z' * ∏ i, (M.project i).transition t (s i) z (a i) (s' i)

def initialHistory (M : Model N T) : History M 0 := fun _ => M.initialSignal

/-- Rooted signal-history probability. This is zero on histories with a different initial signal. -/
def historyProb (M : Model N T) : (t : ℕ) → History M t → ℝ
  | 0, h => if h 0 = M.initialSignal then 1 else 0
  | t + 1, h => historyProb M t (Fin.init h) * M.signal t (h (Fin.last t).castSucc) (h (Fin.last (t+1)))

/-- Uniform-in-N bounds are supplied outside a family; only actual periods and actions count. -/
def Bounded (M : Model N T) (rlo rhi blo bhi : ℝ) : Prop :=
  rlo ≤ rhi ∧ 0 < blo ∧ blo ≤ bhi ∧
  ∀ t < T, ∀ i s z (a : Action M t i s z),
    (rlo ≤ (M.project i).reward t s z a.val ∧ (M.project i).reward t s z a.val ≤ rhi) ∧
    (a.val ≠ 0 → blo ≤ M.consumption t i s z a.val ∧ M.consumption t i s z a.val ≤ bhi)

end BrownSharedSignals.Fluid


