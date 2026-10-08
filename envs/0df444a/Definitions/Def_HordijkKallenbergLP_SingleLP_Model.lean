-- Prove2me | Definitions.Def_HordijkKallenbergLP_SingleLP_Model
-- name    : HordijkKallenbergLP_SingleLP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:33:14.260993+00:00
-- url     : https://prove2.me/theorems/6249fc10-60d1-4e17-bb69-f13e1f1fe1aa
-- title:
--   §2.1 and §3.2: r(f), α-discounted value, discounted and average optimality, superharmonic pairs, the primal and dual LPs, E_x and the selection rule
-- statement:
--   This file fixes the objects of Hordijk and Kallenberg's treatment of a finite Markov decision chain by linear programming. The underlying model is the published stationary MDP: a finite state space $E$, a finite nonempty action set $A(i)$ in each state $i$, rewards $r_{ia}$ and transition probabilities $p_{iaj}$ (nonnegative, summing to $1$ over $j$). A policy $R$ may use the whole history and may randomize; $\varphi_i(R)$ is its lim inf average expected reward and $\varphi_i=\sup_R\varphi_i(R)$.
--
--   1. For a decision rule $f$ with $f(i)\in A(i)$, $r(f)=(r_{if(i)})_{i\in E}$; the matrix $P(f)=(p_{if(i)j})$ is the published transition matrix of $f$.
--   2. The **α-discounted value** of a policy $R$ from state $i$ is
--   $$v_i^\alpha(R)=\sum_{t=1}^\infty \alpha^{t-1}\sum_j\sum_a \mathbf P_R(X_t=j,\,Y_t=a\mid X_1=i)\,r_{ja}.$$
--   $R^*$ is **α-discounted optimal** if $v_i^\alpha(R)\le v_i^\alpha(R^*)$ for every policy $R$ and every $i$. A pure stationary policy $f^\infty$ is **α-discounted optimal for all α near enough to 1** if this holds for every $\alpha\in[\alpha_0,1)$, for some $0\le\alpha_0<1$.
--   3. $R^*$ is **average optimal** if $\varphi_i(R^*)=\varphi_i$ for every $i\in E$.
--   4. A pair $(\tilde\varphi,\tilde u)$ of functions $E\to\mathbb R$ is **superharmonic** if, for all $a\in A(i)$ and $i\in E$,
--   $$\tilde\varphi_i\ge\sum_j p_{iaj}\tilde\varphi_j,\qquad \tilde\varphi_i+\tilde u_i\ge r_{ia}+\sum_j p_{iaj}\tilde u_j .$$
--   5. Given weights $\beta_j$, the **primal program** minimizes $\sum_j\beta_j\tilde\varphi_j$ over superharmonic pairs; an optimal solution is a feasible pair whose objective is at most that of every feasible pair.
--   6. The **dual program** has variables $x_{ia},y_{ia}$ for the admissible pairs $a\in A(i)$, and maximizes $\sum_i\sum_a r_{ia}x_{ia}$ subject to
--   $$\sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia}=0,\qquad \sum_a x_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})y_{ia}=\beta_j,\qquad x_{ia},y_{ia}\ge0,$$
--   for all $j\in E$ (constraints (3), (4), (5)). Optimal means feasible with the largest objective.
--   7. $E_x=\{i\mid \sum_a x_{ia}>0\}$, and a decision rule $f$ follows the **selection rule of Theorem 7** if $x_{if(i)}>0$ for $i\in E_x$ and $y_{if(i)}>0$ for $i\notin E_x$.
--
--   These are the objects in which the paper's single-LP construction of an average optimal pure stationary policy is stated.
--
--   **Formalization Note** The discounted value is the limit of the $N$-epoch discounted reward, computed by the same backward recursion over histories as the published total reward; for $0\le\alpha<1$ the limit exists. Average optimality is Hordijk and Kallenberg's $\varphi(R^*)=\varphi$, not Puterman's stronger criterion in the published file. The dual variables are indexed by the admissible pairs only, so the extreme points of the feasible set are those of the paper's polyhedron.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, pp. 353, 355–357, §2.1, §3.1 (r(f)), §3.2 (Definition, primal LP, dual LP (3)–(5), Theorem 7)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The reward vector `r(f) = (r_{i f(i)})_{i ∈ E}` of a decision rule `f`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, §3.1 (after Theorem 1). The matrix
`P(f) = (p_{i f(i) j})` is the published `MarkovDecisionProcesses.transMatrix M f`. -/
def rewardVec (M : StationaryMDP S A) (f : S → A) : S → ℝ := fun i => M.reward i (f i)

/-- The expected **discounted reward over the first `N` epochs**,
`Σ_{t=1}^{N} α^{t−1} Σ_j Σ_a P_R(X_t = j, Y_t = a | X_1 = i) r_{ja}`, for the policy `R` started at
epoch `t` after history `h` in state `s`, computed by the same backward recursion as the published
`totalReward`, with a factor `α` on the continuation.

Hordijk and Kallenberg (1979), p. 353, §2.1. -/
noncomputable def discReward {M : StationaryMDP S A} (R : AvgHRPolicy M) (α : ℝ) :
    ℕ → ℕ → List (S × A) → S → ℝ
  | 0, _, _, _ => 0
  | (k + 1), t, h, s =>
      ∑ a ∈ M.admissible s, R.q t h s a *
        (M.reward s a + α * ∑ j, M.trans s a j * discReward R α k (t + 1) (h ++ [(s, a)]) j)

/-- The **total expected α-discounted reward**
`v_i^α(R) = Σ_{t=1}^∞ α^{t−1} Σ_j Σ_a P_R(X_t = j, Y_t = a | X_1 = i) · r_{ja}`,
the limit as `N → ∞` of the `N`-epoch discounted reward.

Hordijk and Kallenberg (1979), p. 353, §2.1.

**Formalization Note.** `limUnder` returns an arbitrary value when the limit does not exist. For
`0 ≤ α < 1` the series converges absolutely (finitely many bounded rewards), and every statement
of this mission uses `discValue` only for such `α`. -/
noncomputable def discValue {M : StationaryMDP S A} (R : AvgHRPolicy M) (α : ℝ) (i : S) : ℝ :=
  limUnder atTop (fun N : ℕ => discReward R α N 0 [] i)

/-- `R*` is **α-discounted optimal**: `v_i^α(R*) = v_i^α = sup_R v_i^α(R)` for all `i ∈ E`, stated
as `v_i^α(R) ≤ v_i^α(R*)` for every history-dependent randomized policy `R` and every state `i`.

Hordijk and Kallenberg (1979), p. 353, §2.1.

**Formalization Note.** The supremum is over all policies of §2.1 (`AvgHRPolicy M`); writing the
definition as a comparison avoids a real `⨆`. -/
def IsDiscOptimal (M : StationaryMDP S A) (α : ℝ) (Rstar : AvgHRPolicy M) : Prop :=
  ∀ (R : AvgHRPolicy M) (i : S), discValue R α i ≤ discValue Rstar α i

/-- The pure stationary policy `f^∞` is **α-discounted optimal for all α near enough to 1**: there
is a nonnegative `α₀ < 1` such that `f^∞` is α-discounted optimal for every `α ∈ [α₀, 1)`. This is
the property of the policy `f₀^∞` of Theorem 1 (Blackwell), which Theorems 4 and 5 take as given.

Hordijk and Kallenberg (1979), p. 355, Theorem 1, and the proof of Theorem 5 ("there exists a
nonnegative real number α₀ < 1"). -/
def IsDiscOptimalNearOne (M : StationaryMDP S A) [DecidableEq A] (f : S → A)
    (hf : ∀ i, f i ∈ M.admissible i) : Prop :=
  ∃ α₀ : ℝ, 0 ≤ α₀ ∧ α₀ < 1 ∧
    ∀ α : ℝ, α₀ ≤ α → α < 1 → IsDiscOptimal M α (stationaryPolicy M f hf)

/-- `R*` is **average optimal** in Hordijk and Kallenberg's sense: `φ_i(R*) = φ_i` for all
`i ∈ E`, where `φ_i(R)` is the lim inf average expected reward (`gainInf`) and
`φ_i = sup_R φ_i(R)` (`optGainInf`, the supremum over all history-dependent randomized policies).

Hordijk and Kallenberg (1979), p. 353, §2.1.

**Formalization Note.** This is *not* `MarkovDecisionProcesses.IsAverageOptimal` (Puterman's
(8.1.7), lim inf of `R*` ≥ lim sup of every `R`), which is stronger. `optGainInf` is a genuine
real supremum: `|gainInf R i| ≤ max |r|` for every policy, so the family is bounded. -/
def IsAvgOptimal (M : StationaryMDP S A) (Rstar : AvgHRPolicy M) : Prop :=
  ∀ i : S, gainInf Rstar i = optGainInf M i

/-- A pair of functions `(φ̃, ũ)`, `φ̃ ũ : E → ℝ`, is **superharmonic** if
`φ̃_i ≥ Σ_j p_{iaj} φ̃_j` and `φ̃_i + ũ_i ≥ r_{ia} + Σ_j p_{iaj} ũ_j` for all `a ∈ A(i)`, `i ∈ E`.

Hordijk and Kallenberg (1979), p. 356, Definition. -/
def Superharmonic (M : StationaryMDP S A) (φ u : S → ℝ) : Prop :=
  ∀ i : S, ∀ a ∈ M.admissible i,
    ∑ j, M.trans i a j * φ j ≤ φ i ∧ M.reward i a + ∑ j, M.trans i a j * u j ≤ φ i + u i

/-- `(φ̃, ũ)` is an **optimal solution of the primal linear program** of §3.2,
`minimize Σ_j β_j φ̃_j` subject to `(φ̃, ũ)` superharmonic: it is feasible and its objective is
at most that of every feasible pair.

Hordijk and Kallenberg (1979), p. 356, §3.2. -/
def IsPrimalOptimal (M : StationaryMDP S A) (β : S → ℝ) (φ u : S → ℝ) : Prop :=
  Superharmonic M φ u ∧
    ∀ φ' u' : S → ℝ, Superharmonic M φ' u' → ∑ j, β j * φ j ≤ ∑ j, β j * φ' j

/-- The **admissible state–action pairs** `{(i, a) | i ∈ E, a ∈ A(i)}`, which index the variables
`x_{ia}`, `y_{ia}` of the dual linear program. -/
abbrev Pair (M : StationaryMDP S A) := {p : S × A // p.2 ∈ M.admissible p.1}

/-- `Σ_{a ∈ A(j)} x_{ja}` for a vector `x` indexed by the admissible pairs. -/
noncomputable def stateSum (M : StationaryMDP S A) [DecidableEq S] [DecidableEq A]
    (x : Pair M → ℝ) (j : S) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Pair M => p.1.1 = j), x p

/-- The **feasible set of the dual linear program** (3)–(5): the pairs `(x, y)` of vectors indexed
by the admissible pairs with
* (3) `Σ_i Σ_a (δ_{ij} − p_{iaj}) x_{ia} = 0`, `j ∈ E`;
* (4) `Σ_a x_{ja} + Σ_i Σ_a (δ_{ij} − p_{iaj}) y_{ia} = β_j`, `j ∈ E`;
* (5) `x_{ia}, y_{ia} ≥ 0`, `a ∈ A(i)`, `i ∈ E`.

Hordijk and Kallenberg (1979), p. 357, (3)–(5).

**Formalization Note.** Variables exist only for admissible pairs (`Pair M`), so the feasible set
is a subset of `(Pair M → ℝ) × (Pair M → ℝ)` and its extreme points are those of the paper's
polyhedron. -/
def dualFeasible (M : StationaryMDP S A) [DecidableEq S] [DecidableEq A] (β : S → ℝ) :
    Set ((Pair M → ℝ) × (Pair M → ℝ)) :=
  {z | (∀ j : S, ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.1 p = 0) ∧
       (∀ j : S, stateSum M z.1 j + ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.2 p = β j) ∧
       (∀ p : Pair M, 0 ≤ z.1 p ∧ 0 ≤ z.2 p)}

/-- The objective `Σ_i Σ_a r_{ia} x_{ia}` of the dual linear program.

Hordijk and Kallenberg (1979), p. 357. -/
def dualObjective (M : StationaryMDP S A) [DecidableEq A] (x : Pair M → ℝ) : ℝ :=
  ∑ p : Pair M, M.reward p.1.1 p.1.2 * x p

/-- `(x, y)` is an **optimal solution of the dual linear program**: it is feasible for (3)–(5) and
its objective `Σ r_{ia} x_{ia}` is at least that of every feasible pair.

Hordijk and Kallenberg (1979), p. 357. -/
def IsDualOptimal (M : StationaryMDP S A) [DecidableEq S] [DecidableEq A] (β : S → ℝ)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) : Prop :=
  z ∈ dualFeasible M β ∧ ∀ z' ∈ dualFeasible M β, dualObjective M z'.1 ≤ dualObjective M z.1

/-- `E_x = {i | Σ_a x_{ia} > 0}`.

Hordijk and Kallenberg (1979), p. 357, Theorem 7. -/
def Ex (M : StationaryMDP S A) [DecidableEq S] [DecidableEq A] (x : Pair M → ℝ) : Set S :=
  {i | 0 < stateSum M x i}

/-- The **selection rule of Theorem 7**: the decision rule `f` (with `f(i) = a_i ∈ A(i)`) picks an
action with `x_{i a_i} > 0` for `i ∈ E_x` and an action with `y_{i a_i} > 0` for `i ∉ E_x`.

Hordijk and Kallenberg (1979), p. 357, Theorem 7. -/
def IsSelection (M : StationaryMDP S A) [DecidableEq S] [DecidableEq A] (x y : Pair M → ℝ)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) : Prop :=
  ∀ i : S, (i ∈ Ex M x → 0 < x ⟨(i, f i), hf i⟩) ∧ (i ∉ Ex M x → 0 < y ⟨(i, f i), hf i⟩)

end HordijkKallenbergLP.SingleLP


