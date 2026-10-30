-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_StochasticValues
-- name    : BrownSharedSignals_Fluid_StochasticValues
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:46:52.697382+00:00
-- url     : https://prove2.me/theorems/1719a8bf-ce0c-460e-b501-014f20ab0f87
-- title:
--   Mixed policies, trajectory laws and stochastic value functions
-- statement:
--   A behavioral policy supplies a probability distribution over the Cartesian product of admissible local actions at each project state and complete signal history. Its normalization and its resource feasibility are separate predicates. A local policy supplies one finite action distribution per project, and the independent proposal law is their product.
--
--   The probability of a full finite trajectory is its initial point-mass indicator times the product of its policy action probabilities and joint transition probabilities. Forward state-history masses are defined by summing these one-step transitions; policy values are the backward finite-horizon expected total rewards with zero terminal payoff. The optimal value uses Bellman maximization over feasible actions. This is an operational construction, with no assumed performance inequalities.
--
--   A conditional-state kernel is defined by evolving the projects along a fixed complete signal path, including paths of probability zero. It agrees with ordinary conditioning on positive-probability histories and specifies a version on null histories. Stage expectations include the history probability; conditional expectations use the fixed-path kernel. All sums are finite. Markov policies embed by ignoring the signal-history prefix.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), §2, equations (1)–(2), printed 6–7 / PDF 7–8; §4.1, printed 20–21 / PDF 21–22

import Definitions.Def_BrownSharedSignals_Fluid_Model

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid
variable {N T : ℕ}

/-- Behavioral policies retain signal history. The source's Markov policies embed by
ignoring the prefix; the fluid policy retains its schedule through this history. -/
abbrev Policy (M : Model N T) :=
  (t : ℕ) → (h : History M t) → (s : State M) → Actions M t s (current M h) → ℝ

def IsPolicy (M : Model N T) (π : Policy M) : Prop :=
  ∀ t < T, ∀ h s, (∀ a, 0 ≤ π t h s a) ∧ ∑ a, π t h s a = 1

def IsFeasiblePolicy (M : Model N T) (π : Policy M) : Prop :=
  IsPolicy M π ∧ ∀ t < T, ∀ h s a, π t h s a ≠ 0 → FeasibleAction M t s (current M h) a

abbrev LocalPolicy (M : Model N T) := (t : ℕ) → (h : History M t) →
  (i : Fin N) → (s : Fin (M.stateSize i + 1)) → Arlib.Probability.FinDist (Action M t i s (current M h))

def independentPolicy (M : Model N T) (p : LocalPolicy M) : Policy M :=
  fun t h s a => ∏ i, p t h i (s i) (a i)

/-- Finite one-step conditional expectation, keeping the signal-memory prefix. -/
def nextExpectation (M : Model N T) (t : ℕ) (h : History M t) (s : State M)
    (a : Fin N → ℝ) (v : History M (t+1) → State M → ℝ) : ℝ :=
  ∑ z', ∑ s', transition M t s (current M h) a s' z' * v (Fin.snoc h z') s'

/-- Backward evaluation of the actual mixed controlled process, with zero terminal payoff. -/
def policyValueAux (M : Model N T) (π : Policy M) :
    (k t : ℕ) → History M t → State M → ℝ
  | 0, _, _, _ => 0
  | k+1, t, h, s => ∑ a, π t h s a *
      (reward M t s (current M h) (actionVector M a) +
       nextExpectation M t h s (actionVector M a) (policyValueAux M π k (t+1)))

def policyValue (M : Model N T) (π : Policy M) (t : ℕ) (h : History M t) (s : State M) : ℝ :=
  policyValueAux M π (T-t) t h s

/-- Finite Bellman maximization over the resource-feasible subset, equation (2).
Each maximized set is finite and nonempty (the all-zero action is feasible). -/
def optimalValueAux (M : Model N T) : (k t : ℕ) → History M t → State M → ℝ
  | 0, _, _, _ => 0
  | k+1, t, h, s => sSup {v | ∃ a : Actions M t s (current M h),
      FeasibleAction M t s (current M h) a ∧
      v = reward M t s (current M h) (actionVector M a) +
        nextExpectation M t h s (actionVector M a) (optimalValueAux M k (t+1))}

def optimalValue (M : Model N T) (t : ℕ) (h : History M t) (s : State M) : ℝ :=
  optimalValueAux M (T-t) t h s

/-- Restriction of a complete signal path to its prefix through period t. -/
def historyPrefix (M : Model N T) {n : ℕ} (h : History M n) (t : Fin (n+1)) : History M t.val :=
  fun j => h ⟨j.val, by omega⟩

/-- Probability of a complete finite state/signal/action trajectory. Summing these
masses gives the forward laws below. Action types include only admissible actions. -/
def trajectoryProbability (M : Model N T) (π : Policy M) (n : ℕ)
    (h : History M n) (s : Fin (n+1) → State M)
    (a : (t : Fin n) → Actions M t.val (s t.castSucc) (current M (historyPrefix M h t.castSucc))) : ℝ :=
  (if h 0 = M.initialSignal ∧ s 0 = M.initialState then 1 else 0) *
    ∏ t : Fin n,
      π t.val (historyPrefix M h t.castSucc) (s t.castSucc) (a t) *
      transition M t.val (s t.castSucc) (current M (historyPrefix M h t.castSucc))
        (actionVector M (a t)) (s t.succ) (h t.succ)

/-- Forward law of the controlled trajectory at a complete signal history, including
its probability. Unlike conditioning by division this has a defined null-history value. -/
def stateMass (M : Model N T) (π : Policy M) : (t : ℕ) → History M t → State M → ℝ
  | 0, h, s => if h 0 = M.initialSignal ∧ s = M.initialState then 1 else 0
  | t+1, h, s' => ∑ s, stateMass M π t (Fin.init h) s *
      ∑ a, π t (Fin.init h) s a *
        transition M t s (current M (Fin.init h)) (actionVector M a) s' (current M h)

/-- A kernel version of project-state conditioning, defined by forward evolution
along a fixed signal path even when that path has probability zero. -/
def conditionalState (M : Model N T) (π : Policy M) :
    (t : ℕ) → History M t → State M → ℝ
  | 0, _, s => if s = M.initialState then 1 else 0
  | t+1, h, s' => ∑ s, conditionalState M π t (Fin.init h) s *
      ∑ a, π t (Fin.init h) s a *
        ∏ i, (M.project i).transition t (s i) (current M (Fin.init h)) (a i).val (s' i)

def conditionalActionExpectation (M : Model N T) (π : Policy M) (t : ℕ)
    (h : History M t) (g : (s : State M) → Actions M t s (current M h) → ℝ) : ℝ :=
  ∑ s, conditionalState M π t h s * ∑ a, π t h s a * g s a

def stageExpectation (M : Model N T) (π : Policy M) (t : ℕ)
    (g : (h : History M t) → (s : State M) → Actions M t s (current M h) → ℝ) : ℝ :=
  ∑ h, ∑ s, stateMass M π t h s * ∑ a, π t h s a * g h s a

end BrownSharedSignals.Fluid


