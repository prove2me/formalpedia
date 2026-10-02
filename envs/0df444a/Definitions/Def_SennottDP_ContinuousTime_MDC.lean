-- Prove2me | Definitions.Def_SennottDP_ContinuousTime_MDC
-- name    : SennottDP_ContinuousTime_MDC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T10:43:24.129995+00:00
-- url     : https://prove2.me/theorems/5c98d51d-4e16-41d1-9483-70cfdf92db5a
-- title:
--   Markov decision chain, general policies and the average cost criterion
-- statement:
--   A **Markov decision chain** (MDC) $\Delta$ has a state space $S$; for each state $i$ a finite set $A_i$ of actions; a cost $C(i,a)$; and for each $a\in A_i$ a probability distribution $(P_{ij}(a))_{j\in S}$ of the next state. The MDC is *valid* when every $A_i$ is nonempty, every cost $C(i,a)$, $a\in A_i$, is nonnegative, and $\sum_j P_{ij}(a)=1$ for $a\in A_i$.
--
--   A **policy** $\theta$ is history dependent and may randomize: given the history $h_t=(i_0,a_0,\dots,i_{t-1},a_{t-1},i_t)$ it chooses $a\in A_{i_t}$ with probability $\theta(a\mid h_t)$. Writing $E_\theta[\,\cdot\mid X_0=i]$ for expectation under $\theta$ from the initial state $i$, the **average cost** of $\theta$ and the **minimum average cost** are
--
--   $$J_\theta(i)=\limsup_{n\to\infty}\frac1n\sum_{t=0}^{n-1}E_\theta\big[C(X_t,Y_t)\mid X_0=i\big],\qquad J(i)=\inf_\theta J_\theta(i),$$
--
--   both with values in $[0,\infty]$. A stationary policy $f$ with $f(i)\in A_i$ chooses $f(i)$ in state $i$ whatever the history.
--
--   These are the objects of Chapter 2 of the book; in this mission they are used for the auxiliary MDC $\Delta$ of a continuous time Markov decision chain.
--
--   **Formalization Note** The structure holds the data; the axioms are the predicate `MDC.IsValid`. A history is the list of past state–action pairs, most recent first, with the current state; the probability of a history is computed recursively (`histProb`). Expected costs and the average cost are $[0,\infty]$-valued (`ℝ≥0∞`), with the costs converted by `ENNReal.ofReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 16–27, Sections 2.1–2.4, eqs. (2.15)–(2.16)

import Mathlib

open scoped ENNReal NNReal
open Classical Filter

namespace SennottDP.ContinuousTime

/-- A (discrete time) Markov decision chain (Sennott, §2.1, p. 16): for each state `i` a finite
action set `A i`, costs `C i a`, and transition probabilities `P i a j`. The structure holds the
data only; the axioms of an MDC (nonempty action sets, nonnegative costs, `P i a ·` a probability
distribution for `a ∈ A i`) are the predicate `MDC.IsValid`. -/
structure MDC (S : Type) (Act : Type) where
  A : S → Finset Act
  C : S → Act → ℝ
  P : S → Act → S → ℝ≥0∞

namespace MDC

variable {S Act : Type} (M : MDC S Act)

/-- The axioms of an MDC (§2.1): every action set is nonempty, every cost `C(i,a)`, `a ∈ A i`,
is nonnegative, and `(P_{ij}(a))_j` is a probability distribution for every `a ∈ A i`. -/
def IsValid : Prop :=
  (∀ i, (M.A i).Nonempty) ∧ (∀ i, ∀ a ∈ M.A i, 0 ≤ M.C i a) ∧
    ∀ i, ∀ a ∈ M.A i, ∑' j, M.P i a j = 1

/-- A general (history-dependent, randomized) policy (§2.2, pp. 20–22). A history at time `t`
is `h_t = (i_0, a_0, …, i_{t-1}, a_{t-1}, i_t)`; it is encoded as the list of past state–action
pairs, **most recent first**, together with the current state `i_t`. `σ h i a` is the
probability of choosing `a`; it is a probability distribution on `A i`. -/
structure Policy where
  σ : List (S × Act) → S → Act → ℝ≥0∞
  σ_sum : ∀ h i, ∑ a ∈ M.A i, σ h i a = 1
  σ_supp : ∀ h i a, a ∉ M.A i → σ h i a = 0

variable {M}

/-- `histProb θ i t h j`: the probability, under `θ` from the initial state `i`, that the history
at time `t` is `(h, j)` (past pairs `h`, most recent first, current state `j`) (§2.3). -/
noncomputable def histProb (θ : M.Policy) (i : S) : ℕ → List (S × Act) → S → ℝ≥0∞
  | 0, [], j => if j = i then 1 else 0
  | 0, _ :: _, _ => 0
  | _ + 1, [], _ => 0
  | t + 1, (k, a) :: h, j => histProb θ i t h k * θ.σ h k a * M.P k a j

/-- `E_θ[C(X_t, Y_t) | X_0 = i]`, the expected cost incurred at time `t` (§2.3), in `[0, ∞]`. -/
noncomputable def expectedCost (θ : M.Policy) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : List (S × Act), ∑' j : S, ∑ a ∈ M.A j,
    histProb θ i t h j * θ.σ h j a * ENNReal.ofReal (M.C j a)

/-- The long-run expected average cost of `θ` from `i`, equation (2.15), p. 27:
`J_θ(i) = limsup_{n→∞} (1/n) Σ_{t=0}^{n-1} E_θ[C(X_t,Y_t) | X_0 = i]`, in `[0, ∞]`. -/
noncomputable def avgCost (θ : M.Policy) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => (∑ t ∈ Finset.range n, expectedCost θ i t) / (n : ℝ≥0∞)) atTop

variable (M)

/-- The minimum average cost `J(i) = inf_θ J_θ(i)` over all general policies, equation (2.16),
p. 27. -/
noncomputable def avgValue (i : S) : ℝ≥0∞ :=
  ⨅ θ : M.Policy, avgCost θ i

/-- The stationary policy `f` (with `f i ∈ A i`) viewed as a general policy: at every history
with current state `i` it chooses `f i` with probability one (§2.2, p. 20). -/
noncomputable def ofStationary (f : S → Act) (hf : ∀ i, f i ∈ M.A i) : M.Policy where
  σ _ i a := if a = f i then 1 else 0
  σ_sum _ i := by simp [hf i]
  σ_supp _ i a ha := by
    have : a ≠ f i := fun h => ha (h ▸ hf i)
    simp [this]

end MDC

end SennottDP.ContinuousTime


