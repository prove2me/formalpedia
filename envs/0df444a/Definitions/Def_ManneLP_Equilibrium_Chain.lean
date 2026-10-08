-- Prove2me | Definitions.Def_ManneLP_Equilibrium_Chain
-- name    : ManneLP_Equilibrium_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:53:25.780396+00:00
-- url     : https://prove2.me/theorems/b6f9c69d-cd6b-4e04-abb7-aee22a2f63bd
-- title:
--   §2–§3 — stationary randomized rule, its Markov chain of stock levels, statistical equilibrium (2), and the expected monthly cost (1)
-- statement:
--   This file defines the objects of Manne (1960), §2–§3, that the linear program is meant to optimize.
--
--   1. **Stationary randomized decision rule.** A function $q(j\mid i)\ge 0$, zero unless $(i,j)$ is admissible, with $\sum_{j:(i,j)\in A} q(j\mid i)=1$ for every stock level $i\le T$. It is the conditional probability of producing $j$ at initial stock $i$; mixed strategies are allowed ("the conditional probability of taking action $j$ … may lie anywhere in the closed interval between zero and unity", §2).
--   2. **Its Markov chain.** Under $q$, the initial stock moves from $i$ to $t$ with probability
--   $$
--   P_q(i,t)=\sum_{j:(i,j)\in A} q(j\mid i)\,\Pr\big(\max(0,i+j-n)=t\big).
--   $$
--   3. **Statistical equilibrium** (2). A probability vector $y=(y_0,\dots,y_T)$ ($y_i\ge0$, $\sum_i y_i=1$) is a statistical equilibrium of $q$ if the law of the terminal stock equals the law of the initial stock:
--   $$
--   y_t=\sum_{i=0}^{T} y_i\,P_q(i,t)\qquad(t=0,1,\dots,T),
--   $$
--   that is, $y$ is a stationary distribution of the chain of $q$. It need not be unique: the chain may split into several closed classes (§7 (3)).
--   4. **Joint law** $x_{ij}=y_i\,q(j\mid i)$ of initial stock and production quantity.
--   5. **Expected monthly cost** (1). For a law $x$ of $(i,j)$ on the admissible pairs, with the demand $n$ independent of $(i,j)$ and distributed as $p$, the triple $(i,j,n)$ has law $x_{ij}p_n$, and
--   $$
--   \mathcal E C_1(i)+\mathcal E C_2(j)+\mathcal E C_3(n-k)
--   =\sum_{(i,j)\in A}\sum_{n\ge0}x_{ij}p_nC_1(i)+\sum_{(i,j)\in A}\sum_{n\ge0}x_{ij}p_nC_2(j)+\sum_{(i,j)\in A}\sum_{n\ge0}x_{ij}p_nC_3(n-i-j).
--   $$
--   The expected monthly cost of a rule $q$ in an equilibrium $y$ is this quantity for $x_{ij}=y_iq(j\mid i)$.
--
--   These are the objects over which the paper's criterion, the expected monthly cost under the equilibrium probabilities, is minimized.
--
--   **Formalization Note** The expected cost is defined from the joint law of $(i,j,n)$, not as $\sum c_{ij}x_{ij}$; the identity with the linear objective is a separate statement of the mission. Each sum over $n$ is a `tsum`; for $\mathcal E C_3$ it is meaningful when $\sum_n p_n C_3(n-i-j)$ converges absolutely, which the theorems that use it assume. $y$ is a function on $\mathbb N$ of which only the values at $0,\dots,T$ are used.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), pp. 260–261 (PDF pp. 3–4), §2 (1) and mixed strategies, §3 (2)–(4)

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model

namespace ManneLP.Equilibrium

/-- A stationary randomized decision rule (§2: "mixed strategies are available"): `q i j` is the
conditional probability of producing `j` when the initial stock is `i`. It is nonnegative, vanishes
off the admissible pairs, and sums to one over the admissible actions at every stock level
`i ≤ T`. -/
def IsRule (M : Model) (q : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j) ∧ (∀ i j, (i, j) ∉ M.A → q i j = 0) ∧
    ∀ i, i ≤ M.T → ∑ j ∈ actions M i, q i j = 1

/-- The transition probability of the Markov chain of initial stocks under the rule `q`: from
initial stock `i`, produce `j` with probability `q i j`, then the next month's initial stock is the
terminal stock `max(0, i + j − n)`. -/
noncomputable def trans (M : Model) (q : ℕ → ℕ → ℝ) (i t : ℕ) : ℝ :=
  ∑ j ∈ actions M i, q i j * termProb M (i + j) t

/-- Statistical equilibrium (§3, (2)): `y` is a probability distribution on the stock levels
`0, …, T` that the chain of `q` leaves unchanged, i.e. the law `y'` of the terminal stock equals the
law `y` of the initial stock. It need not be unique. -/
def IsEquilibrium (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : Prop :=
  (∀ i, i ≤ M.T → 0 ≤ y i) ∧ ∑ i ∈ states M, y i = 1 ∧
    ∀ t, t ≤ M.T → y t = ∑ i ∈ states M, y i * trans M q i t

/-- The joint law `xᵢⱼ = yᵢ q(j | i)` of initial stock and production quantity. -/
def jointLaw (y : ℕ → ℝ) (q : ℕ → ℕ → ℝ) : ℕ × ℕ → ℝ :=
  fun a => y a.1 * q a.1 a.2

/-- `ℰC₁(i)` under the joint law `x a · p n` of `(i, j, n)`. -/
noncomputable def expC₁ (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ, x a * M.p n * M.C₁ a.1

/-- `ℰC₂(j)` under the joint law `x a · p n` of `(i, j, n)`. -/
noncomputable def expC₂ (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ, x a * M.p n * M.C₂ a.2

/-- `ℰC₃(n − k)`, `k = i + j`, under the joint law `x a · p n` of `(i, j, n)`. -/
noncomputable def expC₃ (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ, x a * M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ))

/-- The expected monthly cost (1), `ℰC₁(i) + ℰC₂(j) + ℰC₃(n − k)`, when `(i, j)` has law `x` on the
admissible pairs and the demand `n` is independent of `(i, j)` with law `p`. -/
noncomputable def expCost (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  expC₁ M x + expC₂ M x + expC₃ M x

/-- The expected monthly cost (1) of the rule `q` in the statistical equilibrium `y`. -/
noncomputable def eqCost (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  expCost M (jointLaw y q)

end ManneLP.Equilibrium


