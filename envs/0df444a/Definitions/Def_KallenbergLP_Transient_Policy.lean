-- Prove2me | Definitions.Def_KallenbergLP_Transient_Policy
-- name    : KallenbergLP_Transient_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:04:11.82753+00:00
-- url     : https://prove2.me/theorems/667eca89-5a0b-4c5a-afa5-65c7332442c3
-- title:
--   Histories, general policies, occupancies, and transient policies
-- statement:
--   At epoch $t\ge1$, a history records the initial state, all subsequent observed states, and the actions chosen before epoch $t$. A policy $R$ assigns a probability distribution on $A(i_t)$ to every history ending in state $i_t$. Its transition products define $P_R(X_t=j\mid X_1=i)$ and $P_R(X_t=j,Y_t=a\mid X_1=i)$.
--
--   A policy is **transient** when
--
--   $$\sum_{t=1}^{\infty}P_R(X_t=j\mid X_1=i)<\infty\qquad(i,j\in E).$$
--
--   Pure stationary policies choose one admissible action per state at every epoch. Memoryless policies may depend on the epoch and current state. These distinctions are needed to compare the policy classes in Theorem 3.2.4.
--
--   **Formalization Note** Histories with inadmissible earlier actions are present in the finite encoding, but their probability is zero because every decision rule assigns zero probability to actions outside the admissible set.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 20–23, Section 2.2

import Definitions.Def_KallenbergLP_Transient_MDP
set_option autoImplicit false

namespace KallenbergLP.Transient

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- A history at epoch `n + 1`: `n + 1` states and `n` already chosen actions. -/
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

/-- General randomized, history-dependent policies from §2.2. -/
structure Policy (M : MDP N α) where
  choose : ∀ n, History N α n → α → ℝ
  choose_nonneg : ∀ n h a, 0 ≤ choose n h a
  choose_outside : ∀ n h a, a ∉ M.actions h.last → choose n h a = 0
  choose_sum_one : ∀ n h, (∑ a : α, choose n h a) = 1

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

/-- The probability of a history, conditional on its first state. -/
def historyProb (M : MDP N α) (R : Policy M) (i : Fin N)
    (n : ℕ) (h : History N α n) : ℝ :=
  (if h.states ⟨0, by omega⟩ = i then 1 else 0) *
    ∏ k : Fin n,
      R.choose k.val (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k)
          (h.states ⟨k.val + 1, by omega⟩)

/-- Probability that the state at epoch `n + 1` is `j`, starting from `i`. -/
def stateProb (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) : ℝ :=
  ∑ h : History N α n, if h.last = j then historyProb M R i n h else 0

/-- Joint probability of state `j` and action `a` at epoch `n + 1`. -/
def occupancy (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α)
    (n : ℕ) : ℝ :=
  ∑ h : History N α n,
    if h.last = j then historyProb M R i n h * R.choose n h a else 0

/-- A policy is transient if every state has finite expected visit count. -/
def IsTransient (M : MDP N α) (R : Policy M) : Prop :=
  ∀ i j : Fin N, Summable (fun n : ℕ => stateProb M R i j n)

/-- A policy whose decisions depend only on time and the current state. -/
def Memoryless (M : MDP N α) (R : Policy M) : Prop :=
  ∃ q : ℕ → Fin N → α → ℝ,
    ∀ n (h : History N α n) a, R.choose n h a = q n h.last a

end KallenbergLP.Transient


