-- Prove2me | Definitions.Def_PutermanMDP_TotalReward_Bellman
-- name    : PutermanMDP_TotalReward_Bellman
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:07.079003+00:00
-- url     : https://prove2.me/theorems/c05f6395-62b7-4163-8b13-1fcad4fe5caa
-- title:
--   Undiscounted Bellman operator, nonnegative class, and zero-start iteration
-- statement:
--   For a discrete probability distribution $p$ and an extended-real function $v$ on states, form its signed expectation as the nonnegative expectation of $v^+$ minus that of $v^-$. For a model with reward $r$ and transition probabilities $p$, set
--   $$
--   (\mathcal Lv)(s)=\sup_{a\in A_s}\left\{r(s,a)+\sum_t p(t\mid s,a)v(t)\right\},\qquad
--   V^+=\{v:0\le v(s)<\infty\text{ for every }s\}.
--   $$
--   The iteration is defined by $v^0(s)=0$ for every state and $v^{n+1}=\mathcal Lv^n$. No maximizing action is selected and no attainment is assumed.
--
--   This specifies the operator and the actual algorithm independently of the optimal expected reward.
--
--   **Formalization Note** Sums of positive and negative parts are computed in extended nonnegative reals before subtraction in extended reals. The Bellman theorems use nonnegative arguments, for which the negative part is zero; the totalized signed expectation outside its defined domain has no probabilistic interpretation. $V^+$ requires pointwise finiteness, not a uniform bound, and the definitions do not assert that $\mathcal L$ preserves $V^+$.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, pp. 280–281, 285, 294 (PDF 296–297, 301, 310), Eq. (7.1.5), §7.2.1 and Theorem 7.2.12 recurrence

import Mathlib
import Definitions.Def_PutermanMDP_TotalReward_Model
open scoped ENNReal

namespace PutermanMDP.TotalReward

/-- Expectation of an extended value under a discrete probability distribution,
as the difference of nonnegative expectations. Bellman results below apply this
only to nonnegative values, where the negative expectation is zero. -/
noncomputable def transitionValue {S : Type*} (p : PMF S) (v : S → EReal) : EReal :=
  ((∑' t : S, p t * (v t).toENNReal : ℝ≥0∞) : EReal) -
    ((∑' t : S, p t * (-v t).toENNReal : ℝ≥0∞) : EReal)

/-- Component form of the undiscounted optimality operator (7.1.5).
The supremum is over all admissible actions; attainment is not required. -/
noncomputable def bellman {S : Type*} {A : S → Type*}
    (M : Model S A) (v : S → EReal) (s : S) : EReal :=
  ⨆ a : A s, (M.reward s a : EReal) + transitionValue (M.transition s a) v

/-- The pointwise-finite nonnegative class V⁺ on p. 285. It is not the class
of uniformly bounded functions. Bellman is not assumed to preserve this class. -/
def InVPlus {S : Type*} (v : S → EReal) : Prop :=
  ∀ s : S, 0 ≤ v s ∧ v s < ⊤

/-- The actual recurrence in Theorem 7.2.12, with the initial vector exactly zero.
Extended values make this a total definition without defaulting divergent sums to zero. -/
noncomputable def valueIterate {S : Type*} {A : S → Type*}
    (M : Model S A) : ℕ → S → EReal
  | 0 => fun _ => 0
  | n + 1 => bellman M (valueIterate M n)

end PutermanMDP.TotalReward


