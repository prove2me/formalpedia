-- Prove2me | Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
-- name    : HordijkKallenbergLP_ExtremePoint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:37:28.523263+00:00
-- url     : https://prove2.me/theorems/44acbb43-ad2f-4e46-9fe9-bbe7c117714a
-- title:
--   §2.1, (3)–(5), (6): admissible pairs, the dual feasible set, stationary rules, P(π), ergodic sets, γ and the representative (x(π), y(π))
-- statement:
--   Fix a Markov decision chain with a finite state space $E$, for each state $i$ a finite nonempty set $A(i)$ of actions, rewards $r_{ia}$ and transition probabilities $p_{iaj}\ge 0$ with $\sum_j p_{iaj}=1$ (the published model `StationaryMDP`). Fix weights $\beta_j$ on the states. This file defines the objects of Hordijk and Kallenberg's §3.3.
--
--   1. **The dual feasible set.** The variables are $x_{ia}, y_{ia}$, one pair for each state $i$ and admissible action $a\in A(i)$. A pair $(x,y)$ is feasible when
--   $$
--   \begin{aligned}
--   &\textstyle\sum_i\sum_a(\delta_{ij}-p_{iaj})\,x_{ia}=0, && j\in E, &(3)\\
--   &\textstyle\sum_a x_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})\,y_{ia}=\beta_j, && j\in E, &(4)\\
--   &x_{ia}\ge 0,\quad y_{ia}\ge 0, && a\in A(i),\ i\in E. &(5)
--   \end{aligned}
--   $$
--   2. **Stationary rules.** A stationary (randomized) rule $\pi=(\pi_{ia})$ puts nonnegative weights on $A(i)$ summing to one; the rule of a pure policy $f^\infty$ with $f(i)\in A(i)$ is $\pi_{ia}=1$ if $a=f(i)$ and $0$ otherwise. Its transition matrix is $P(\pi)=\big(\sum_{a\in A(i)}p_{iaj}\pi_{ia}\big)_{ij}$; for a pure rule this is $P(f)=(p_{if(i)j})$.
--   3. **Ergodic sets.** For a transition matrix $P$, the ergodic set of a recurrent state $l$ is the set of states accessible from $l$; a state that is not recurrent is transient, and $T$ is the set of transient states.
--   4. **The representative.** With $P^*(\pi)$ the Cesàro limit matrix and $D(\pi)=(I-P(\pi)+P^*(\pi))^{-1}-P^*(\pi)$ the deviation matrix of $P(\pi)$,
--   $$
--   x_{ia}(\pi)=\big[\beta^TP^*(\pi)\big]_i\,\pi_{ia},\qquad y_{ia}(\pi)=\big[\beta^TD(\pi)+\gamma^TP^*(\pi)\big]_i\,\pi_{ia},\qquad a\in A(i),\ i\in E,\qquad (6)
--   $$
--   where $\gamma_l=0$ for $l\in T$ and, for $l$ in an ergodic set $E_j$,
--   $$
--   \gamma_l=\max_{i\in E_j}\frac{-\sum_k\beta_k d_{ki}(\pi)}{\sum_{k\in E_j}p^*_{ki}(\pi)}.
--   $$
--
--   These definitions are the vocabulary of Theorem 10: the representative of a pure stationary policy is an extreme point of the dual feasible set.
--
--   **Formalization Note.** The LP variables are functions on the subtype of admissible pairs, so there is no coordinate for a non-admissible action. $P^*$ and $D$ are the published `limitMatrix` and `deviationMatrix`; their defining identities are Blackwell's Lemma 1(a), 1(d). The paper prints the denominator of $\gamma_l$ as $\sum_k p^*_{ki}(\pi)$ over all $k$; that is a misprint (with it, the two-state chain $0\to1$, $1\to1$ gives $y_1=-\beta_0/2<0$), and the denominator $\sum_{k\in E_j}p^*_{ki}(\pi)$ used here is the one that the feasibility proof on p. 360 and the proof of Theorem 10 on p. 362 need. The maximum is taken over the finite nonempty ergodic set.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 353 (§2.1), p. 357 ((3)–(5)), p. 359 (§3.3, (6))

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix

namespace HordijkKallenbergLP.ExtremePoint

open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- An **admissible state–action pair** `(i, a)` with `a ∈ A(i)`. The dual linear program
(3)–(5) of Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, has one variable `x_ia` and one variable
`y_ia` for each such pair and no others. -/
abbrev Pair (M : StationaryMDP S A) : Type _ := {p : S × A // p.2 ∈ M.admissible p.1}

/-- The **feasible set of the dual linear program** (3)–(5), Hordijk and Kallenberg (1979), p. 357:
the pairs `(x, y)` of vectors indexed by the admissible pairs with
* (3) `∑_i ∑_a (δ_ij − p_iaj) x_ia = 0` for every `j ∈ E`;
* (4) `∑_a x_ja + ∑_i ∑_a (δ_ij − p_iaj) y_ia = β_j` for every `j ∈ E`;
* (5) `x_ia ≥ 0`, `y_ia ≥ 0` for every `a ∈ A(i)`, `i ∈ E`.

All sums over `a` run over `A(i)`, i.e. over the admissible pairs.

**Formalization Note.** The variables are indexed by the subtype `Pair M` of admissible pairs, so
there are no free coordinates for non-admissible actions; extreme points of this set are the
extreme points of the paper's polyhedron. The objective `∑ r_ia x_ia` is not part of the
feasible set. -/
def dualFeasible (M : StationaryMDP S A) (β : S → ℝ) :
    Set ((Pair M → ℝ) × (Pair M → ℝ)) :=
  { z | (∀ j : S, ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.1 p = 0) ∧
        (∀ j : S, (∑ p : Pair M, if p.1.1 = j then z.1 p else 0) +
          ∑ p : Pair M,
            ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.2 p = β j) ∧
        (∀ p : Pair M, 0 ≤ z.1 p) ∧
        (∀ p : Pair M, 0 ≤ z.2 p) }

/-- A **(randomized) stationary decision rule** `π = (π_ia)`: nonnegative weights on the
admissible actions of each state, summing to one, Hordijk and Kallenberg (1979), §2.1, p. 353
(the policy `π^∞` uses it at every epoch).

**Formalization Note.** Values `π i a` for `a ∉ A(i)` are never used by any definition below. -/
def IsStationaryRule (M : StationaryMDP S A) (π : S → A → ℝ) : Prop :=
  (∀ i a, a ∈ M.admissible i → 0 ≤ π i a) ∧ ∀ i, ∑ a ∈ M.admissible i, π i a = 1

/-- The rule `π_ia = 1` if `a = f(i)` and `0` otherwise, of a **pure** stationary policy `f^∞`,
Hordijk and Kallenberg (1979), §2.1, p. 353. -/
def pureRule (f : S → A) : S → A → ℝ := fun i a => if a = f i then 1 else 0

/-- The transition matrix `P(π) = (∑_a p_iaj π_ia)` of a stationary rule, Hordijk and Kallenberg
(1979), §3.3, p. 359 (sum over `a ∈ A(i)`). For `π = pureRule f` with `f(i) ∈ A(i)` it is
`P(f) = (p_{if(i)j})` of p. 355, i.e. `MarkovDecisionProcesses.transMatrix M f`. -/
def policyMatrix (M : StationaryMDP S A) (π : S → A → ℝ) : Matrix S S ℝ :=
  fun i j => ∑ a ∈ M.admissible i, M.trans i a j * π i a

/-- The **ergodic set** of a state `l`: the states accessible from `l` under the transition
matrix `P`. When `l` is recurrent (`IsRecurrent P l`) this is the closed recurrent class
`E_j ∋ l` of Hordijk and Kallenberg (1979), §3.3, p. 359. -/
noncomputable def ergodicSet (P : Matrix S S ℝ) (l : S) : Finset S := by
  classical
  exact Finset.univ.filter (fun i => Accessible P l i)

omit [DecidableEq S] in
/-- The ergodic set of `l` contains `l` (accessibility is reflexive). -/
theorem mem_ergodicSet_self (P : Matrix S S ℝ) (l : S) : l ∈ ergodicSet P l := by
  classical
  simp only [ergodicSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Relation.ReflTransGen.refl

/-- The vector `γ` of (6), Hordijk and Kallenberg (1979), §3.3, p. 359, for the chain `P = P(π)`
with limit matrix `P* = limitMatrix P` and deviation matrix `D = deviationMatrix P`:
`γ_l = 0` for a transient state `l ∈ T`, and for `l` in the ergodic set `E_j`,
`γ_l = max_{i ∈ E_j} (−∑_k β_k d_ki) / (∑_{k ∈ E_j} p*_ki)`.

**Formalization Note (corrected misprint).** The page prints the denominator as `∑_k p*_ki`, the
sum over *all* `k ∈ E`. With that denominator the representative (6) is in general not feasible:
for the two-state chain `0 → 1`, `1 → 1` (state 0 transient) one gets `y_1 = −β_0/2 < 0`. The
nonnegativity argument on p. 360 ("for i ∈ E_j: y_ia(π) = {∑_k β_k d_ki + γ_i ∑_{k∈E_j} p*_ki}·π_ia ≥ 0")
and the zero `ȳ_{i(k)}(f) = 0` used on p. 362 both require the denominator `∑_{k ∈ E_j} p*_ki`,
which is the one used here. The max is a `Finset.sup'` over the (nonempty, finite) ergodic set
of `l`; the denominator is positive for recurrent `i` (a theorem, `p*_ii > 0`), so Lean's
`x / 0 = 0` convention is never reached on a Markov matrix. -/
noncomputable def gamma (P : Matrix S S ℝ) (β : S → ℝ) (l : S) : ℝ := by
  classical
  exact if IsRecurrent P l then
    (ergodicSet P l).sup' ⟨l, mem_ergodicSet_self P l⟩
      (fun i => (-(∑ k, β k * deviationMatrix P k i)) /
        (∑ k ∈ ergodicSet P l, limitMatrix P k i))
  else 0

/-- The `x`-part of the **representative** (6), Hordijk and Kallenberg (1979), §3.3, p. 359:
`x_ia(π) = [β^T P*(π)]_i · π_ia`, `a ∈ A(i)`, `i ∈ E`. -/
noncomputable def repX (M : StationaryMDP S A) (β : S → ℝ) (π : S → A → ℝ) : Pair M → ℝ :=
  fun p => (β ᵥ* limitMatrix (policyMatrix M π)) p.1.1 * π p.1.1 p.1.2

/-- The `y`-part of the **representative** (6), Hordijk and Kallenberg (1979), §3.3, p. 359:
`y_ia(π) = [β^T D(π) + γ^T P*(π)]_i · π_ia`, `a ∈ A(i)`, `i ∈ E`, with `γ` as in `gamma`. -/
noncomputable def repY (M : StationaryMDP S A) (β : S → ℝ) (π : S → A → ℝ) : Pair M → ℝ :=
  fun p => (β ᵥ* deviationMatrix (policyMatrix M π) +
      gamma (policyMatrix M π) β ᵥ* limitMatrix (policyMatrix M π)) p.1.1 * π p.1.1 p.1.2

end HordijkKallenbergLP.ExtremePoint


