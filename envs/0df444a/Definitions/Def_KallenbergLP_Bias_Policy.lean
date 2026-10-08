-- Prove2me | Definitions.Def_KallenbergLP_Bias_Policy
-- name    : KallenbergLP_Bias_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:32:42.391329+00:00
-- url     : https://prove2.me/theorems/decc8a67-0ad5-4e23-96ee-6c839b2316d2
-- title:
--   History-dependent randomized policies and pure stationary policies
-- statement:
--   At period $t\ge1$, a **history** records the states $i_1,\ldots,i_t$ and the earlier actions $a_1,\ldots,a_{t-1}$. A general **policy** $R$ gives, at every such history, nonnegative probabilities for actions at the current state, zero outside $A(i_t)$ and summing to one. Thus policies may depend on the entire past and may randomize.
--
--   A **pure stationary policy** $f^\infty\in C_D$ chooses one admissible action $f(i)\in A(i)$ in every state and period. The file also defines the finite product probability of a history conditional on its initial state and the joint state-action probability
--
--   $$
--   p^t_{ija}(R)=\Pr_R(X_t=j,Y_t=a\mid X_1=i).
--   $$
--
--   These probabilities supply the reward criteria for all policies, including those outside the Markov and stationary subclasses.
--
--   **Formalization Note** A Lean history with parameter $n$ describes the book's period $t=n+1$. Histories with an inadmissible earlier action are represented but have zero probability under every admissible policy.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 20–21, Section 2.2; https://ir.cwi.nl/pub/13008

import Definitions.Def_KallenbergLP_Bias_MDP

namespace KallenbergLP.Bias

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- A history at time `n + 1`: `n + 1` states and `n` earlier actions. -/
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

/-- An admissible randomized decision rule at every finite history, hence a policy in C. -/
structure Policy (M : MDP N α) where
  choose : ∀ n, History N α n → α → ℝ
  choose_nonneg : ∀ n h a, 0 ≤ choose n h a
  choose_outside : ∀ n h a, a ∉ M.actions h.last → choose n h a = 0
  choose_sum_one : ∀ n h, (∑ a : α, choose n h a) = 1

/-- A selector of one admissible action in each state, representing C_D. -/
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

/-- Probability of a complete history, conditional on the initial state. -/
def historyProb (M : MDP N α) (R : Policy M) (i : Fin N)
    (n : ℕ) (h : History N α n) : ℝ :=
  (if h.states ⟨0, by omega⟩ = i then 1 else 0) *
    ∏ k : Fin n,
      R.choose k.val (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k)
          (h.states ⟨k.val + 1, by omega⟩)

/-- Joint probability of state `j` and action `a` in period `n + 1`. -/
def occupancy (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α)
    (n : ℕ) : ℝ :=
  ∑ h : History N α n,
    if h.last = j then historyProb M R i n h * R.choose n h a else 0

end KallenbergLP.Bias


