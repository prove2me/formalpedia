-- Prove2me | Definitions.Def_PutermanMDP_TotalReward_Model
-- name    : PutermanMDP_TotalReward_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:16.928993+00:00
-- url     : https://prove2.me/theorems/e237ef09-1af1-483f-b6f5-2e8e47841102
-- title:
--   Discrete total-reward model and admissible history policies
-- statement:
--   Let $S$ be the state space and $A_s$ the actions available at state $s$. A time-homogeneous model specifies a real reward $r(s,a)$ and a probability distribution $p(\cdot\mid s,a)$ on successor states. A history consists of all previous state–action pairs, in chronological order, and the current state. A history-dependent randomized policy assigns a probability distribution on $A_s$ to each such history. A randomized Markov policy depends only on the epoch and current state.
--
--   Starting from $s$, the law of the history is the point mass at the empty past and $s$, then successively samples the policy's action and the model's next state. For $r^+=\max(r,0)$ and $r^-=\max(-r,0)$ define
--   $$
--   v^\pi_\pm(s)=\sum_{n=0}^{\infty}\mathbb E_s^\pi[r^\pm(X_n,Y_n)],\qquad
--   v^\pi(s)=v^\pi_+(s)-v^\pi_-(s),\qquad
--   v^*(s)=\sup_{\pi\in\Pi^{HR}}v^\pi(s).
--   $$
--   Assumption 7.1.1 requires at least one of $v^\pi_+(s),v^\pi_-(s)$ to be finite for every policy and state. A positive bounded model requires $v^\pi_+(s)<\infty$ for every policy and state, and at least one action of nonnegative immediate reward at every state. The bound may depend on both policy and state.
--
--   These definitions separate probability laws and expected rewards from optimality claims.
--
--   **Formalization Note** The theorem binders require nonempty countable states and nonempty countable action types, following the discrete-space convention of §2.1.2. The definition layer itself is polymorphic. Probability mass functions enforce normalization. Nonnegative sums use extended nonnegative reals; values and suprema use extended reals. The subtraction is interpreted as an expected reward only under the finiteness assumption; its totalized value when both parts are infinite has no reward interpretation. Epoch zero corresponds to the book's first decision epoch.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, pp. 18, 21–24, 278–279, 284 (PDF 34, 37–40, 294–295, 300), §§2.1.2–2.2, Eqs. (7.1.2)–(7.1.3), Assumptions 7.1.1, 7.2.1–7.2.2

import Mathlib
open scoped ENNReal

namespace PutermanMDP.TotalReward

/-- The time-homogeneous discrete model of §§2.1 and 7.1. Actions depend on the state.
Countability and nonemptiness are imposed by each theorem, not finiteness. -/
structure Model (S : Type*) (A : S → Type*) where
  reward : (s : S) → A s → ℝ
  transition : (s : S) → A s → PMF S

/-- Observable history: the preceding state/action pairs in chronological order,
followed by the current state. Its list length is the zero-based decision epoch. -/
abbrev History (S : Type*) (A : S → Type*) := List (Sigma A) × S

/-- All admissible history-dependent randomized policies, including decisions on
histories of probability zero. The dependent action type enforces admissibility. -/
abbrev HRPolicy (S : Type*) (A : S → Type*) := (h : History S A) → PMF (A h.2)

/-- Time-dependent randomized Markov policies. -/
abbrev MRPolicy (S : Type*) (A : S → Type*) := ℕ → (s : S) → PMF (A s)

def markovPolicy {S : Type*} {A : S → Type*} (π : MRPolicy S A) : HRPolicy S A :=
  fun h => π h.1.length h.2

/-- The distribution of the observable history at epoch n, constructed from the
actual transition and action distributions; n=0 precedes the first reward. -/
noncomputable def historyLaw {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : ℕ → PMF (History S A)
  | 0 => PMF.pure ([], s)
  | n + 1 => (historyLaw M π s n).bind fun h =>
      (π h).bind fun a => (M.transition h.2 a).bind fun t =>
        PMF.pure (h.1 ++ [⟨h.2, a⟩], t)

/-- Expected accumulated nonnegative stage rewards, computed using the finite
history laws. ENNReal sums retain divergence as +∞. The generic payoff g may
itself equal +∞, including at a single state/action; zero probability times
this infinite payoff is zero. The later reward-part definitions specialize g
to finite one-step values, but that is not a restriction of this helper. -/
noncomputable def accumulated {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S)
    (g : (t : S) → A t → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' h : History S A, ∑' a : A h.2,
    historyLaw M π s n h * π h a * g h.2 a

noncomputable def positiveReward {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : ℝ≥0∞ :=
  accumulated M π s (fun t a => ENNReal.ofReal (M.reward t a))

noncomputable def negativeReward {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : ℝ≥0∞ :=
  accumulated M π s (fun t a => ENNReal.ofReal (-M.reward t a))

/-- Assumption 7.1.1: at least one expected reward part is finite, separately
for every history-dependent randomized policy and starting state. -/
def WellDefined {S : Type*} {A : S → Type*} (M : Model S A) : Prop :=
  ∀ (π : HRPolicy S A) (s : S),
    positiveReward M π s < ⊤ ∨ negativeReward M π s < ⊤

/-- Total expected reward, used only under WellDefined or PositiveBounded.
The excluded case +∞−+∞ has EReal's totalized value, not a reward interpretation. -/
noncomputable def policyValue {S : Type*} {A : S → Type*}
    (M : Model S A) (π : HRPolicy S A) (s : S) : EReal :=
  (positiveReward M π s : EReal) - (negativeReward M π s : EReal)

/-- Equation (7.1.3): the supremum over all admissible HR policies, separately
at each initial state. Extended suprema preserve unbounded values. -/
noncomputable def optimalValue {S : Type*} {A : S → Type*}
    (M : Model S A) (s : S) : EReal :=
  ⨆ π : HRPolicy S A, policyValue M π s

/-- Exactly Assumptions 7.2.1 and 7.2.2. No uniform upper bound, optimal
policy, nonnegative reward for every action, or Bellman identity is assumed. -/
def PositiveBounded {S : Type*} {A : S → Type*} (M : Model S A) : Prop :=
  (∀ (π : HRPolicy S A) (s : S), positiveReward M π s < ⊤) ∧
  (∀ s : S, ∃ a : A s, 0 ≤ M.reward s a)

end PutermanMDP.TotalReward


