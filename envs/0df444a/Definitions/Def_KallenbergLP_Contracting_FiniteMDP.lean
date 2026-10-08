-- Prove2me | Definitions.Def_KallenbergLP_Contracting_FiniteMDP
-- name    : KallenbergLP_Contracting_FiniteMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:58:29.685032+00:00
-- url     : https://prove2.me/theorems/bd316e0e-d5a7-41a1-b1d1-4c9bd57a3462
-- title:
--   Finite substochastic Markov decision model and history-dependent policies
-- statement:
--   A finite Markov decision model has a finite state set $E$, a finite action set $A(i)$ at each state, a real reward $r_{ia}$, and transition probabilities $p_{iaj}\ge 0$ with $\sum_j p_{iaj}\le 1$. The missing probability is the chance that the process terminates. The chapter theorems require the state set and every action set to be nonempty.
--
--   A history at time $t=n+1$ records the preceding $n$ state-action pairs and the current state. A general policy assigns a probability distribution over available actions to every such history. Markov rules depend only on time and current state, stationary rules only on state, and pure stationary rules choose one action per state.
--
--   For any policy $R$, $P_R(X_t=j,Y_t=a\mid X_1=i)$ is computed from the product of its decision probabilities and the transition probabilities, summed over all histories ending at $(j,a)$. The total expected reward and the state-action frequency vector are the corresponding infinite sums. These common definitions make the four policy classes comparable without identifying them.
--
--   **Formalization Note** Lean indexes time from zero: index $n$ represents the book's period $t=n+1$. Actions use a type family $A(i)$, so there are no illegal state-action pairs.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 19–23, Section 2.2; p. 55, equation (3.3.12)

import Mathlib

namespace KallenbergLP.Contracting

/-! The finite, possibly terminating decision model of Kallenberg, §2.2. -/

variable (E : Type) [Fintype E] (A : E → Type) [∀ i, Fintype (A i)]

/-- A history at the beginning of period `n + 1`. Its first `n` entries are
state–action pairs, and its second component is the current state. -/
abbrev History (n : ℕ) := (Fin n → Σ i : E, A i) × E

/-- A randomized decision rule may depend on the entire history. -/
abbrev Policy := ∀ n : ℕ, (h : History E A n) → A h.2 → ℝ

/-- A stationary randomized decision rule. -/
abbrev StationaryRule := ∀ i : E, A i → ℝ

/-- A pure stationary decision rule. -/
abbrev PureRule := ∀ i : E, A i

/-- The model allows termination after a transition: rows need only sum to at most one. -/
structure FiniteMDP where
  transition : ∀ i : E, A i → E → ℝ
  reward : ∀ i : E, A i → ℝ
  transition_nonneg : ∀ i a j, 0 ≤ transition i a j
  transition_substochastic : ∀ i a, (∑ j, transition i a j) ≤ 1

variable {E A}

/-- A valid probability distribution over actions for every possible history. -/
def IsPolicy (π : Policy E A) : Prop :=
  (∀ n h a, 0 ≤ π n h a) ∧
  (∀ n h, ∑ a, π n h a = 1)

def IsStationaryRule (q : StationaryRule E A) : Prop :=
  (∀ i a, 0 ≤ q i a) ∧ (∀ i, ∑ a, q i a = 1)

def stationaryPolicy (q : StationaryRule E A) : Policy E A :=
  fun _ h a => q h.2 a

noncomputable def pureRule (f : PureRule E A) : StationaryRule E A := by
  classical
  exact fun i a => if a = f i then 1 else 0

noncomputable def purePolicy (f : PureRule E A) :
    Policy E A := stationaryPolicy (pureRule f)

/-- A policy is Markov when its decision rule depends on time and current state only. -/
def IsMarkov (π : Policy E A) : Prop :=
  ∃ q : ℕ → StationaryRule E A, ∀ n h a, π n h a = q n h.2 a

namespace FiniteMDP

variable (M : FiniteMDP E A)

/-- Probability of a complete history from initial state `i`. The stage index is
zero based in Lean, so stage `n` represents the book's time `t = n + 1`. -/
noncomputable def historyProbability (π : Policy E A) (i : E) :
    ∀ n : ℕ, History E A n → ℝ
  | 0, h => by
      classical
      exact if h.2 = i then 1 else 0
  | n + 1, h => by
      let previous : History E A n :=
        (fun k => h.1 (Fin.castSucc k), (h.1 (Fin.last n)).1)
      exact historyProbability π i n previous *
        π n previous (h.1 (Fin.last n)).2 *
        M.transition previous.2 (h.1 (Fin.last n)).2 h.2

/-- `P_R(X_t=j,Y_t=a | X₁=i)` with `t = n + 1`. -/
noncomputable def stateActionProbability (π : Policy E A) (i j : E)
    (a : A j) (n : ℕ) : ℝ :=
  ∑ actions : Fin n → Σ k : E, A k,
    M.historyProbability π i n (actions, j) * π n (actions, j) a

/-- The total expected reward for each initial state, expressed as the
absolutely convergent series guaranteed by contraction. -/
noncomputable def totalReward (π : Policy E A) (i : E) : ℝ :=
  ∑' n : ℕ, ∑ j : E, ∑ a : A j,
    M.stateActionProbability π i j a n * M.reward j a

/-- The state–action frequency vector (3.3.12), now for any policy. -/
noncomputable def frequency (β : E → ℝ) (π : Policy E A) :
    StationaryRule E A :=
  fun j a => ∑' n : ℕ, ∑ i : E, β i * M.stateActionProbability π i j a n

end FiniteMDP

end KallenbergLP.Contracting


