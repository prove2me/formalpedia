-- Prove2me | Definitions.Def_KallenbergLP_Positive_Policy
-- name    : KallenbergLP_Positive_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:05.477911+00:00
-- url     : https://prove2.me/theorems/854b8b04-341d-4356-926c-0f072cb9ca4d
-- title:
--   Section 2.2 — history dependent randomized policies and finite history probabilities
-- statement:
--   A **history** before the $(n+1)$st action consists of the initial state, the next $n$ observed states, and the $n$ actions previously chosen. A **policy** $R=(\pi^1,\pi^2,\ldots)$ assigns, at every such history ending in state $i$, a probability distribution over $A(i)$. Its choice may depend on the whole history and on time. Thus the policy class $C$ includes nonstationary, non-Markov and randomized policies.
--
--   A **pure stationary rule** $f$ chooses one admissible action $f(i)\in A(i)$ for each state. The associated policy $f^\infty$ always takes that action when in state $i$. For an initial state $i$, the probability of a finite history is the product of its successive action probabilities and transition probabilities; histories with a different initial state have probability zero. The joint probability that the process occupies state $j$ and chooses action $a$ at time $n+1$ is the sum of those history probabilities times the current action probability.
--
--   These finite probabilities define the expected reward without restricting the comparison class to transient or stationary policies.
--
--   **Formalization Note** Lean uses `n=0` for the first decision, corresponding to the book's time $t=1$. Policy probabilities vanish outside $A(i)$ and sum to one over all actions. Termination is represented by the missing mass of a substochastic transition row.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 20–22 (PDF pp. 28–30), Section 2.2

import Definitions.Def_KallenbergLP_Positive_MDP

namespace KallenbergLP.Positive

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- A history before decision `n + 1`: `n + 1` states and `n` past actions. -/
structure History (N : ℕ) (α : Type) (n : ℕ) where
  states : Fin (n + 1) → Fin N
  chosen : Fin n → α

instance (n : ℕ) : Fintype (History N α n) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (n + 1) → Fin N) × (Fin n → α))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun h => (h.states, h.chosen)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro h; cases h; rfl }

def History.last {n : ℕ} (h : History N α n) : Fin N := h.states ⟨n, by omega⟩

def History.prefix {n : ℕ} (h : History N α n) (k : Fin n) : History N α k.val where
  states := fun i => h.states ⟨i.val, by omega⟩
  chosen := fun i => h.chosen ⟨i.val, by omega⟩

/-- A member of `C`: a randomized decision rule at every time and history. -/
structure Policy (M : MDP N α) where
  choose : ∀ n, History N α n → α → ℝ
  choose_nonneg : ∀ n h a, 0 ≤ choose n h a
  choose_outside : ∀ n h a, a ∉ M.actions h.last → choose n h a = 0
  choose_sum_one : ∀ n h, (∑ a : α, choose n h a) = 1

/-- An admissible deterministic stationary decision rule. -/
structure PureRule (M : MDP N α) where
  choose : Fin N → α
  admissible : ∀ i, choose i ∈ M.actions i

def purePolicy (M : MDP N α) (f : PureRule M) : Policy M where
  choose := fun _ h a => if a = f.choose h.last then 1 else 0
  choose_nonneg := by intros; split_ifs <;> norm_num
  choose_outside := by
    intro n h a ha
    have hne : a ≠ f.choose h.last := by
      intro heq
      exact ha (heq ▸ f.admissible h.last)
    simp [hne]
  choose_sum_one := by
    intro n h
    classical
    simp

/-- Probability of a history conditional on initial state `i`. Zero policy
weights suppress histories containing inadmissible actions. -/
def historyProb (M : MDP N α) (R : Policy M) (i : Fin N)
    (n : ℕ) (h : History N α n) : ℝ :=
  (if h.states ⟨0, by omega⟩ = i then 1 else 0) *
    ∏ k : Fin n,
      R.choose k.val (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k)
          (h.states ⟨k.val + 1, by omega⟩)

/-- Joint probability of state `j` and action `a` at time `n + 1`. -/
def occupancy (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α)
    (n : ℕ) : ℝ :=
  ∑ h : History N α n,
    if h.last = j then historyProb M R i n h * R.choose n h a else 0

end KallenbergLP.Positive


