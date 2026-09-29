-- Prove2me | Definitions.Def_JewellMRP_Discounted_MRP
-- name    : JewellMRP_Discounted_MRP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:57:57.45818+00:00
-- url     : https://prove2.me/theorems/39385b65-862d-49b7-b209-1587e77d7bdb
-- title:
--   Markov-renewal program: transition probabilities, sojourn-time distributions, one-transition discounted returns, $\tilde f$, $\tilde q$ and the test quantity
-- statement:
--   This file sets up the finite **Markov-renewal program** of Jewell (1963), Sections *Markov-Renewal Processes*, *The Reward Structure* and *The Decision Process* (pp. 940–942), together with the transforms used in equations (5)–(7), (14), (15) and Fig. 1.
--
--   Let $S$ be a finite set of states (the paper's $i = 1, \dots, N$) and $A$ a finite set of alternatives (the paper's $z = 1, \dots, Z$), every alternative being available in every state. A Markov-renewal program consists of:
--
--   1. for each alternative $z$ and states $i, j$, a **transition probability** $p^z_{ij} \ge 0$ with $\sum_j p^z_{ij} = 1$ (eq. (1));
--   2. for each $z, i, j$, a **sojourn-time distribution** $F^z_{ij}$, the law of the transition interval $\tau(i,j)$ (eq. (2)): a probability distribution on the real line that gives no mass to $(-\infty, 0]$, i.e. $\tau \ge 0$ and $F^z_{ij}(0) = 0$ (p. 941);
--   3. for each continuous discount factor $\alpha$ and each $z, i, j$, a real number $\rho^z_{ij}(\alpha)$, the expected discounted return earned during a transition from $i$ to $j$ under $z$ (eq. (4)).
--
--   From these data the file defines the **Laplace–Stieltjes transform** (7)
--   $$
--   \tilde f^z_{ij}(s) = \int_0^\infty e^{-st}\, dF^z_{ij}(t),
--   $$
--   the entries $\tilde q^z_{ij}(s) = p^z_{ij}\,\tilde f^z_{ij}(s)$ of the matrix $\tilde q(s)$ (p. 945), the **average one-step discounted return** (5)
--   $$
--   \rho^z_i(\alpha) = \sum_{j} p^z_{ij}\,\rho^z_{ij}(\alpha),
--   $$
--   the **test quantity** of Fig. 1 against a vector of returns $v = (v_j)_{j \in S}$,
--   $$
--   \rho^z_i(\alpha) + \sum_{j} p^z_{ij}\,\tilde f^z_{ij}(\alpha)\, v_j ,
--   $$
--   and its maximum over the alternatives $z$ (the right-hand side of (6) and (14)).
--
--   These are the objects on which every statement of the mission is built: the transform $\tilde f$ carries the whole influence of the sojourn times on discounting.
--
--   **Formalization Note** States and alternatives are arbitrary finite types (a relabelling of $\{1,\dots,N\}$ and $\{1,\dots,Z\}$); the maximum over alternatives needs $A$ nonempty, which is assumed where it is used. The one-transition returns $\rho^z_{ij}(\alpha)$ are taken as arbitrary real data instead of being computed from reward functions $R^z_{ij}(x\mid\tau)$ by the Stieltjes integral (4); every result of the mission therefore holds for arbitrary finite one-transition returns, which includes those produced by (4). The transform (7) is integrated over $(0,\infty)$, which carries all the mass of $F^z_{ij}$, so it equals the paper's integral over $[0,\infty)$; for $s > 0$ the integrand is bounded by $1$ there.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, pp. 940-942 (Markov-Renewal Processes, eqs. (1)-(2), F_ij(0) = 0 on p. 941; The Reward Structure, eqs. (4)-(5); The Decision Process), eq. (7) on p. 942, q̃(s) on p. 945, test quantity of Fig. 1 on p. 947

import Mathlib

namespace JewellMRP.Discounted

open MeasureTheory

/-- A finite **Markov-renewal program** (Jewell 1963, pp. 940–942), for one fixed family of
one-transition discounted returns.

* `S` is the finite set of states `1, …, N` and `A` the finite set of alternatives
  `1, …, Z`; every alternative is available in every state.
* `p z i j` is the transition probability `p^z_{ij}` of (1): each `p z` is a stochastic matrix.
* `F z i j` is the law of the transition interval `τ(i, j)` under alternative `z`, i.e. the
  distribution `F^z_{ij}` of (2): a probability measure on `ℝ` giving no mass to `(-∞, 0]`
  (the interval is nonnegative and `F_{ij}(0) = 0`, p. 941).
* `ρ α z i j` is the expected discounted return `ρ^z_{ij}(α)` earned during a transition from
  `i` to `j` under alternative `z` with continuous discount factor `α`, eq. (4); here it is
  arbitrary real data. -/
structure MRP (S A : Type*) [Fintype S] where
  /-- Transition probabilities `p^z_{ij}`. -/
  p : A → S → S → ℝ
  p_nonneg : ∀ z i j, 0 ≤ p z i j
  p_sum : ∀ z i, ∑ j, p z i j = 1
  /-- Sojourn-time distributions `F^z_{ij}`. -/
  F : A → S → S → Measure ℝ
  F_prob : ∀ z i j, IsProbabilityMeasure (F z i j)
  /-- `τ ≥ 0` and `F^z_{ij}(0) = Pr{τ ≤ 0} = 0`. -/
  F_Iic_zero : ∀ z i j, F z i j (Set.Iic 0) = 0
  /-- One-transition expected discounted returns `ρ^z_{ij}(α)`. -/
  ρ : ℝ → A → S → S → ℝ

variable {S A : Type*} [Fintype S]

/-- The Laplace–Stieltjes transform (7) of the sojourn distribution:
`f̃^z_{ij}(s) = ∫_0^∞ e^{-s t} dF^z_{ij}(t)`. The integral is taken over `(0, ∞)`, which carries
all the mass of `F^z_{ij}`. -/
noncomputable def ftilde (M : MRP S A) (z : A) (i j : S) (s : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂(M.F z i j)

/-- The entries of the matrix `q̃(s) = [p^z_{ij} f̃^z_{ij}(s)]` (p. 945), for alternative `z`. -/
noncomputable def qtilde (M : MRP S A) (s : ℝ) (z : A) (i j : S) : ℝ :=
  M.p z i j * ftilde M z i j s

/-- The average one-step discounted return (5): `ρ^z_i(α) = Σ_j p^z_{ij} ρ^z_{ij}(α)`. -/
def rhoState (M : MRP S A) (α : ℝ) (z : A) (i : S) : ℝ :=
  ∑ j, M.p z i j * M.ρ α z i j

/-- The test quantity of Fig. 1 for alternative `z` in state `i` against returns `v`:
`ρ^z_i(α) + Σ_j p^z_{ij} f̃^z_{ij}(α) v_j`. -/
noncomputable def test (M : MRP S A) (α : ℝ) (z : A) (i : S) (v : S → ℝ) : ℝ :=
  rhoState M α z i + ∑ j, qtilde M α z i j * v j

/-- The maximal test quantity `max_z [ρ^z_i(α) + Σ_j p^z_{ij} f̃^z_{ij}(α) v_j]` of (6), (14)
and Fig. 1. -/
noncomputable def maxTest [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (v : S → ℝ) (i : S) :
    ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun z => test M α z i v)

end JewellMRP.Discounted


