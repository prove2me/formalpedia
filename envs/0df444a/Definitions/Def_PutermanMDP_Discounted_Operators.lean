-- Prove2me | Definitions.Def_PutermanMDP_Discounted_Operators
-- name    : PutermanMDP_Discounted_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:30.68114+00:00
-- url     : https://prove2.me/theorems/4d9e5426-a9f2-4997-820c-f14391c33eff
-- title:
--   Bellman operators and the variable-order modified policy iteration algorithm
-- statement:
--   For a deterministic rule $d$, write $(P_dv)(s)=\sum_jp(j\mid s,d(s))v(j)$ and $L_dv=r_d+\lambda P_dv$. Randomized rules average the same expression over their action distributions. Define
--   $$\mathcal Lv(s)=\sup_{a\in A_s}\left\{r(s,a)+\lambda\sum_jp(j\mid s,a)v(j)\right\},\qquad Bv=\mathcal Lv-v.$$
--   When every bounded $v$ has a maximizing decision rule, this is the book's $L$. A rule is greedy at $v$ when $L_dv=Lv$, and $V_B=\{v\in V:Bv\ge0\}$.
--
--   Let $A_d^mw=\sum_{k=0}^m\lambda^kP_d^kw$. The auxiliary operators are $U^mv=\max_d\{A_d^mr_d+\lambda^{m+1}P_d^{m+1}v\}$ and $W_d^mv=v+A_d^mBv$, with $d$ greedy at $v$. An outer MPI run with arbitrary orders $m_n\in\mathbb N$ selects $d_{n+1}$ greedy at $v^n$, retaining the previous rule whenever possible, and computes
--   $$v^{n+1}=L_{d_{n+1}}^{m_n+1}v^n.$$
--   The stop test is performed after the initial greedy evaluation and before the $m_n$ further evaluations. The returned policy repeats $d_{n+1}$ forever.
--
--   **Formalization Note** The formal rule sequence uses $d(n)$ for the book's $d_{n+1}$. The infinite run describes the recurrence continued past a possible stop; the algorithm stops at its first passing index. For $\lambda>0$, the test is exactly $\|Lv-v\|<\varepsilon(1-\lambda)/(2\lambda)$. The printed quotient is encoded as a partial real threshold: the test succeeds exactly when there exists $t\in\mathbb R$ with
--   $$(2\lambda)t=\varepsilon(1-\lambda),\qquad\|Lv-v\|<t.$$
--   For positive discount this is the printed test. When $\lambda=0$ and $\varepsilon>0$, there is no such real threshold and the test cannot succeed. This preserves the source's undefined endpoint rather than assigning a value to division by zero or inventing immediate termination. The full-domain termination claim remains in the goal and the defect is recorded in INSIGHTS.yaml.
--
--   The auxiliary $U^m$ takes a bounded input and a separate witness that the block maximum is attained at each state, then selects its actual maximum value. This witness is not a hypothesis of the MPI goal. One-step Bellman attainment is not silently used as a proof of block attainment.
--
--   Differences from the source:
--   - encoding: L on its attained domain and ℒ otherwise → one statewise Bellman supremum, with MaxAttained recording global one-step attainment; reason: both numerical operators agree whenever the source maximum exists
--   - encoding: U^m and W^m in (6.5.9)–(6.5.10) → U takes a bounded input and a witness of pointwise block attainment; W takes the chosen decision rule explicitly; reason: U evaluates an actual maximum; W equals the source operator when its supplied rule is greedy; block attainment is not assumed by the goal
--   - encoding: algorithm steps 2–3, including retention of the previous greedy rule → MPIRun uses d n for source d_(n+1), retains greedy ties, and applies the policy operator m n + 1 times; reason: the infinite continuation has the same executed prefix up to the separately tested first stop
--   - encoding: the printed partial threshold ε(1−λ)/(2λ), with ε>0 → Stop requires a real t satisfying (2λ)t=ε(1−λ) and residual norm < t; reason: agrees with the printed strict comparison for positive discount and exposes the undefined zero-discount endpoint without a corrective branch
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 186 (PDF 202), §6.5.1, pp. 186–190 (PDF 202–206), Eqs. (6.5.2)–(6.5.10); §§6.1–6.2; DOI 10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Discounted_Model

open MeasureTheory ProbabilityTheory

namespace PutermanMDP.Discounted

/- Imported dependency source, copied verbatim for tool-free blind auditing.
The active declarations are supplied by the imports above.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PutermanMDP.Discounted

/-- A stationary Markov decision process with a nonempty countable state space
and nonempty standard Borel admissible actions at each state. This general object
contains only rewards and transition probabilities; boundedness and discounting
belong to the separate discounted Model. -/
structure MDP (S : Type) [Countable S] [Nonempty S] (A : S → Type)
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] where
  reward : (s : S) → A s → ℝ
  reward_measurable : ∀ s, Measurable (reward s)
  trans : (s : S) → A s → S → ℝ
  trans_nonneg : ∀ s a j, 0 ≤ trans s a j
  trans_sum : ∀ s a, HasSum (trans s a) 1
  trans_measurable : ∀ s j, Measurable (fun a => trans s a j)

variable {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)]

/-- A history before decision `t` records `t` past state/action pairs.
The current state is passed separately. Decisions start at zero. Its sigma algebra
is the finite product of the disjoint-union sigma algebra on Sigma A. -/
abbrev History (A : S → Type) (t : ℕ) := Fin t → Sigma A

/-- Behavioral policies: a probability kernel on admissible actions, for every
observable history and current state. Kernel measurability is the usual
admissibility condition for general (possibly uncountable) action spaces. -/
structure Policy (A : S → Type) [∀ s, MeasurableSpace (A s)] where
  action : (t : ℕ) → (s : S) → Kernel (History A t) (A s)
  stochastic : ∀ t s, IsMarkovKernel (action t s)

/-- Deterministic Markov decision rules. -/
abbrev DecisionRule (A : S → Type) := (s : S) → A s

/-- Randomized Markov decision rules. -/
abbrev RandomRule (A : S → Type) [∀ s, MeasurableSpace (A s)] :=
  (s : S) → ProbabilityMeasure (A s)

/-- Repeating a deterministic decision rule forever. -/
noncomputable def stationary (d : DecisionRule A) : Policy A where
  action := fun _ s => Kernel.deterministic (fun _ => d s) measurable_const
  stochastic := by intros; infer_instance

/-- Repeating a randomized decision rule forever. -/
noncomputable def stationaryRandom (d : RandomRule A) : Policy A where
  action := fun t s => Kernel.const (History A t) (d s : Measure (A s))
  stochastic := by intros; infer_instance

end PutermanMDP.Discounted

import Mathlib
import Definitions.Def_PutermanMDP_Discounted_MDP

open MeasureTheory ProbabilityTheory

namespace PutermanMDP.Discounted

/-- The bounded discounted specialization of the general stationary MDP.
Neither optimality nor convergence is part of the model data. -/
structure Model (S : Type) [Countable S] [Nonempty S] (A : S → Type)
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] extends MDP S A where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  reward_bounded : ∀ s a, |reward s a| ≤ bound
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

variable {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)]

/-- Expected reward `n` transitions after the supplied history. Iterated
conditional expectation integrates actions and sums the countable next states.
The Model fields and Policy.stochastic imply that every stage is measurable in h
and bounded in absolute value by M.bound: the base stage integrates a bounded
measurable reward, and each successor averages such rewards with probability rows
and a Markov kernel. Thus the integrands are integrable and the state sums are
absolutely summable; these are consequences of the data, not extra assumptions. -/
noncomputable def expectedReward (M : Model S A) (π : Policy A) :
    ℕ → (t : ℕ) → History A t → S → ℝ
  | 0, t, h, s => ∫ a, M.reward s a ∂(π.action t s h)
  | n + 1, t, h, s => ∫ a, (∑' j : S, M.trans s a j *
      expectedReward M π n (t + 1) (Fin.snoc h ⟨s, a⟩) j) ∂(π.action t s h)

/-- The expected total discounted reward, not a Bellman fixed-point definition.
Uniform boundedness and discount < 1 give absolute convergence, with
|value M π s| ≤ M.bound / (1 - M.discount), uniformly over π and s. -/
noncomputable def value (M : Model S A) (π : Policy A) (s : S) : ℝ :=
  ∑' n : ℕ, M.discount ^ n * expectedReward M π n 0 (fun i => Fin.elim0 i) s

/-- Supremum over all admissible randomized history-dependent policies.
This class is nonempty (constant deterministic rules) and its values have the
uniform bound M.bound / (1 - M.discount). No empty/unbounded supremum occurs. -/
noncomputable def optimalValue (M : Model S A) (s : S) : ℝ :=
  ⨆ π : Policy A, value M π s

/-- Epsilon optimality uniformly over initial states and against every
history-dependent randomized policy. -/
def EpsilonOptimal (M : Model S A) (ε : ℝ) (π : Policy A) : Prop :=
  ∀ s, optimalValue M s ≤ value M π s + ε

/-- The vector space V of bounded real functions, as a predicate. -/
def BoundedValue (v : S → ℝ) : Prop := ∃ C : ℝ, ∀ s, |v s| ≤ C

/-- Sup norm, used only for bounded functions. -/
noncomputable def supNorm (v : S → ℝ) : ℝ := ⨆ s, |v s|

end PutermanMDP.Discounted

-/

variable {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)]

/-- The stochastic transition operator for a deterministic rule. -/
noncomputable def transition (M : Model S A) (d : DecisionRule A) (v : S → ℝ) : S → ℝ :=
  fun s => ∑' j : S, M.trans s (d s) j * v j

/-- L_d v = r_d + λ P_d v. -/
noncomputable def policyOperator (M : Model S A) (d : DecisionRule A)
    (v : S → ℝ) : S → ℝ := fun s => M.reward s (d s) + M.discount * transition M d v s

/-- The same operator for a randomized Markov rule. -/
noncomputable def randomOperator (M : Model S A) (d : RandomRule A)
    (v : S → ℝ) : S → ℝ := fun s =>
  ∫ a, (M.reward s a + M.discount * ∑' j : S, M.trans s a j * v j) ∂(d s : Measure (A s))

/-- The supremum Bellman operator ℒ; under attainment it is also the book's L. -/
noncomputable def bellman (M : Model S A) (v : S → ℝ) : S → ℝ := fun s =>
  ⨆ a : A s, M.reward s a + M.discount * ∑' j : S, M.trans s a j * v j

/-- D_v consists of rules attaining the statewise Bellman supremum. -/
def Greedy (M : Model S A) (v : S → ℝ) (d : DecisionRule A) : Prop :=
  policyOperator M d v = bellman M v

/-- The standing maximizer assumption wherever the book uses L rather than ℒ. -/
def MaxAttained (M : Model S A) : Prop :=
  ∀ v : S → ℝ, BoundedValue v → ∃ d : DecisionRule A, Greedy M v d

/-- The residual Bv = Lv - v. -/
noncomputable def residual (M : Model S A) (v : S → ℝ) : S → ℝ := bellman M v - v

/-- The initial cone V_B. -/
def VB (M : Model S A) (v : S → ℝ) : Prop :=
  BoundedValue v ∧ ∀ s, 0 ≤ residual M v s

/-- Truncated Neumann series Σ_{k=0}^m (λP_d)^k w. -/
noncomputable def neumann (M : Model S A) (d : DecisionRule A) (m : ℕ)
    (w : S → ℝ) : S → ℝ := fun s =>
  ∑ k ∈ Finset.range (m + 1), M.discount ^ k * (transition M d)^[k] w s

/-- The stationary block return inside the maximum in (6.5.9). -/
noncomputable def blockReturn (M : Model S A) (d : DecisionRule A)
    (m : ℕ) (v : S → ℝ) : S → ℝ := fun s =>
  neumann M d m (fun j => M.reward j (d j)) s +
    M.discount ^ (m + 1) * (transition M d)^[m + 1] v s

/-- The domain condition for the pointwise maximum printed in (6.5.9).
This is separate from one-step Bellman attainment; it is not assumed to follow
from it. It is not a premise of the MPI convergence theorem. -/
def BlockMaxAttained (M : Model S A) (m : ℕ) (v : S → ℝ) : Prop :=
  ∀ s, ∃ d : DecisionRule A, ∀ e : DecisionRule A,
    blockReturn M e m v s ≤ blockReturn M d m v s

/-- Equation (6.5.9) on its stated bounded domain, with actual maximum
attainment. The proof argument excludes a supremum-only extension. -/
noncomputable def U (M : Model S A) (m : ℕ) (v : S → ℝ)
    (_hv : BoundedValue v) (hmax : BlockMaxAttained M m v) : S → ℝ :=
  fun s => blockReturn M (Classical.choose (hmax s)) m v s

/-- Equation (6.5.10); the selected rule is supplied explicitly and required
to be greedy at v when this expression represents W^m v. -/
noncomputable def W (M : Model S A) (d : DecisionRule A)
    (m : ℕ) (v : S → ℝ) : S → ℝ := v + neumann M d m (residual M v)

/-- The untruncated outer run of steps 2--3 of MPI. `d n` is the book's d_{n+1}.
One initial greedy evaluation is followed by m_n further evaluations. The
previous rule is retained whenever it remains greedy, as required in step 2.
Stopping is tested separately, before these further evaluations. -/
def MPIRun (M : Model S A) (m : ℕ → ℕ) (v : ℕ → S → ℝ)
    (d : ℕ → DecisionRule A) : Prop :=
  ∀ n, Greedy M (v n) (d n) ∧
    (∀ k, n = k + 1 → Greedy M (v n) (d k) → d n = d k) ∧
    v (n + 1) = (policyOperator M (d n))^[m n + 1] (v n)

/-- Step 3(b), retaining the printed partial real quotient.
The threshold exists exactly when a real t satisfies 2λt = ε(1-λ).
For ε > 0 and 0 < λ < 1 this is precisely the printed strict comparison.
At λ = 0 there is no such threshold: Stop is false, rather than assigning
an arbitrary real value to division by zero or inserting a new stop branch. -/
def Stop (M : Model S A) (ε : ℝ) (v : S → ℝ) : Prop :=
  ∃ t : ℝ, (2 * M.discount) * t = ε * (1 - M.discount) ∧
    supNorm (residual M v) < t

end PutermanMDP.Discounted


