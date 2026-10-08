-- Prove2me | Definitions.Def_MyersonBargaining_NashSolution_Model
-- name    : MyersonBargaining_NashSolution_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:31.750771+00:00
-- url     : https://prove2.me/theorems/edaf1dbb-cce7-429e-917d-9520edcd1dfe
-- title:
--   Bayesian collective choice problems, conditional beliefs, mechanisms, and incentive-feasible allocations
-- statement:
--   A **Bayesian collective choice problem** has a nonempty finite set of players $I$, a nonempty finite type set $A_i$ for each player $i$, a nonempty finite choice set $C$, real utilities $U_i(c,\alpha)$, and a common prior $P$ on type profiles $\alpha\in\prod_i A_i$. The prior is nonnegative and sums to one. Each marginal type probability $R_i(a_i)$ is positive.
--
--   The marginal and conditional probabilities are
--
--   $$
--   R_i(a_i)=\sum_{\beta:\beta_i=a_i}P(\beta),\qquad
--   P_i(\alpha\mid a_i)=\begin{cases}P(\alpha)/R_i(a_i)&\alpha_i=a_i,\\0&\alpha_i\ne a_i.\end{cases}
--   $$
--
--   A **choice mechanism** $\pi(c\mid s)$ assigns a nonnegative probability to each $c\in C$ at each response profile $s$, with $\sum_c\pi(c\mid s)=1$. For direct mechanisms, the responses are reported types. If type $a_i$ reports $b_i$, its conditional expected payoff is
--
--   $$
--   Z_i(\pi,b_i\mid a_i)=\sum_{\alpha,c}P_i(\alpha\mid a_i)\pi(c\mid\alpha_{-i},b_i)U_i(c,\alpha).
--   $$
--
--   The mechanism is **Bayesian incentive-compatible** when $Z_i(\pi,b_i\mid a_i)\le Z_i(\pi,a_i\mid a_i)$ for every $i,a_i,b_i$. Its interim allocation vector has coordinates $V_{i,a_i}(\pi)=Z_i(\pi,a_i\mid a_i)$. The feasible set $F$ consists of the vectors from all direct choice mechanisms, and $F^*$ consists of those from direct choice mechanisms that also satisfy incentive compatibility. These objects supply the finite-dimensional model for the bargaining result.
--
--   **Formalization Note** Allocations are functions on the disjoint union $\sum_i A_i$. The explicit requirement $R_i(a_i)>0$ makes every conditional probability in equation (3) defined. The prior may assign zero probability to individual type profiles. The model is the consistent (common-prior) reading of (3)–(4); the subjective reading the paper allows on p. 63 is not formalized. Mechanisms are plain real functions with the constraints (2) as a predicate, and the misreport $(\alpha_{-i},b_i)$ replaces only coordinate $i$ of the profile, while $U_i$ is evaluated at the true profile $\alpha$.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), pp. 61–64, Eqs. (1)–(10)

import Mathlib

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Equation (4): the marginal probability of player `i` having type `a`. -/
noncomputable def marginal (P : (∀ i, A i) → ℝ) (i : ι) (a : A i) : ℝ :=
  ∑ β ∈ Finset.univ.filter (fun β => β i = a), P β

/-- Equation (3): the conditional probability of profile `α` given player `i`'s type `a`. -/
noncomputable def cond (P : (∀ i, A i) → ℝ) (i : ι) (α : ∀ i, A i) (a : A i) : ℝ :=
  if α i = a then P α / marginal P i a else 0

/-- Equation (1), with the positive marginals required for equation (3). -/
structure Problem (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : ι → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] (C : Type) [Fintype C] [DecidableEq C] [Nonempty C] where
  U : ι → C → (∀ i, A i) → ℝ
  P : (∀ i, A i) → ℝ
  P_nonneg : ∀ α, 0 ≤ P α
  P_sum : ∑ α, P α = 1
  marginal_pos : ∀ i (a : A i), 0 < marginal P i a

/-- Equation (2): a lottery on `C` for every response profile. -/
def IsChoiceMechanism {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) : Prop :=
  (∀ c s, 0 ≤ π c s) ∧ ∀ s, ∑ c, π c s = 1

/-- Equation (5): expected utility when player `i`, truly of type `a`, reports `b`. -/
noncomputable def Z (G : Problem ι A C) (i : ι)
    (π : C → (∀ i, A i) → ℝ) (b a : A i) : ℝ :=
  ∑ α, ∑ c, cond G.P i α a * π c (Function.update α i b) * G.U i c α

/-- Equation (6): no player type gains from a unilateral false report. -/
def IsBIC (G : Problem ι A C) (π : C → (∀ i, A i) → ℝ) : Prop :=
  ∀ i (a b : A i), Z G i π b a ≤ Z G i π a a

/-- Equations (7)–(8): the interim payoff vector indexed by player and type. -/
noncomputable def V (G : Problem ι A C) (π : C → (∀ i, A i) → ℝ) :
    (Σ i, A i) → ℝ :=
  fun x => Z G x.1 π x.2 x.2

/-- Equation (9): interim payoffs attained by direct choice mechanisms. -/
def F (G : Problem ι A C) : Set ((Σ i, A i) → ℝ) :=
  {x | ∃ π : C → (∀ i, A i) → ℝ, IsChoiceMechanism π ∧ V G π = x}

/-- Equation (10): interim payoffs attained by Bayesian incentive-compatible mechanisms. -/
def FStar (G : Problem ι A C) : Set ((Σ i, A i) → ℝ) :=
  {x | ∃ π : C → (∀ i, A i) → ℝ,
    IsChoiceMechanism π ∧ IsBIC G π ∧ V G π = x}

end MyersonBargaining.NashSolution


