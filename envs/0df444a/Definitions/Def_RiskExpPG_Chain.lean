-- Prove2me | Definitions.Def_RiskExpPG_Chain
-- name    : RiskExpPG_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:45.416981+00:00
-- url     : https://prove2.me/theorems/68d349b2-48f3-4e25-af11-0bda5c9d45e1
-- title:
--   Finite Markov chains: the risk-sensitive cost, excursions to a recurrent state, and return-time moments
-- statement:
--   Let $Q$ be a stochastic matrix on a finite set $\mathcal X$, let $c:\mathcal X\to\mathbb R$ be a one-step cost, and let $\alpha\in\mathbb R$. This file defines the objects of a single chain.
--
--   1. The **expected exponential cost** $E^Q_{\Phi_0=x}\big[\exp\big(\alpha\sum_{i=0}^{n-1}c(\Phi_i)\big)\big]$, as the explicit sum over trajectories of their probability times the exponential.
--   2. The **risk-sensitive cost**
--   $$\Lambda=\lim_{n\to\infty}\frac1n\ln E^Q_{\Phi_0=x}\Big[\exp\Big(\alpha\sum_{i=0}^{n-1}c(\Phi_i)\Big)\Big],$$
--   and the matrix $\widehat P:=\mathrm{diag}(e^{\alpha c})\,Q$.
--   3. **Excursions.** For a state $x^*$, an excursion is a finite list of states different from $x^*$. Started at $x$, the list $l$ stands for the trajectory $x,l,x^*$, whose first return time $\tau_{x^*}:=\inf\{i\ge1:\Phi_i=x^*\}$ is the length of $l$ plus one. Its probability is the product of $Q$ over the $\tau_{x^*}$ transitions.
--   4. **Expectations over excursions**, with values in $[0,\infty]$ for nonnegative functions and as a real sum for vector-valued functions.
--   5. The function $E^Q_{\Phi_0=x}\big[\exp\big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha c(\Phi_i)-\Lambda)\big)\big]$ and the moment $E^Q_{\Phi_0=x}[R^{\tau_{x^*}}]$.
--   6. The predicate that a set of matrices has **uniform return moments**: there is $\overline R>1$ such that for any $R\in(1,\overline R)$ there are $m(R),M(R)\in(1,\infty)$ with $m(R)<E^Q_{\Phi_0=x}[R^{\tau_{x^*}}]<M(R)$ for all $Q$ in the set and all $x$, and $M(R)\downarrow1$ as $R\downarrow1$.
--
--   These objects describe the chain with a frozen parameter. Everything else in the mission is built on them.
--
--   **Formalization Note** The expected exponential cost is not defined by the matrix form, which is part of Proposition 2. Expectations over excursions sum over the event $\{\tau_{x^*}<\infty\}$, which has probability one for the chains of this mission. The risk-sensitive cost uses `limUnder`, and Proposition 2 proves that the limit exists.
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, §2, p.3, Eq. (1); App. A.1, p.15, Eq. (13), (14), Proposition 2; Corollary 1, p.17; Lemma 1, p.22

import Mathlib

open Filter Topology
open scoped ENNReal

namespace RiskExpPG

/-- A real square matrix is **stochastic** when its entries are nonnegative and each row sums to
`1` (Moharrami, Murthy, Roy & Srikant, arXiv:2202.04157v2, §2, p.3, "elements of P̄ are
stochastic"). -/
def IsStochastic {X : Type*} [Fintype X] (Q : Matrix X X ℝ) : Prop :=
  (∀ x y, 0 ≤ Q x y) ∧ ∀ x, ∑ y, Q x y = 1

/-- The trajectory `Φ₀ = x, Φ₁ = y 0, …, Φₙ = y (n-1)` as a function on `Fin (n + 1)`. -/
def traj {X : Type*} {n : ℕ} (x : X) (y : Fin n → X) : Fin (n + 1) → X :=
  Fin.cons x y

/-- `E^Q_{Φ₀ = x}[exp(α Σ_{i=0}^{n-1} c(Φᵢ))]`, the expectation inside Eq. (1) (p.3) and Eq. (13)
(p.15), written out as the sum over the trajectories `(Φ₁, …, Φₙ)` of their probability under the
transition matrix `Q` times the exponential.

**Formalization Note** The matrix form of Eq. (14) is not used as the definition: it is part of
Proposition 2. At `n = 0` the value is `1`, the empty case. -/
noncomputable def expMoment {X : Type*} [Fintype X] (Q : Matrix X X ℝ) (c : X → ℝ) (α : ℝ)
    (x : X) (n : ℕ) : ℝ :=
  ∑ y : Fin n → X,
    (∏ i : Fin n, Q (traj x y i.castSucc) (traj x y i.succ)) *
      Real.exp (α * ∑ i : Fin n, c (traj x y i.castSucc))

/-- The risk-sensitive cost `lim_{n→∞} (1/n) ln E^Q_{Φ₀ = x}[exp(α Σ_{i<n} c(Φᵢ))]` of the chain
`Q` with one-step cost `c` and risk factor `α`, from the initial state `x` (Eq. (1), p.3 and
Eq. (13), p.15).

**Formalization Note** `limUnder` returns an arbitrary value when the limit does not exist.
Proposition 2 proves that the limit exists and does not depend on `x` for a primitive chain. -/
noncomputable def riskRate {X : Type*} [Fintype X] (Q : Matrix X X ℝ) (c : X → ℝ) (α : ℝ)
    (x : X) : ℝ :=
  limUnder atTop fun n : ℕ => (1 / (n : ℝ)) * Real.log (expMoment Q c α x n)

/-- The matrix `P̂ := diag(e^{αc}) Q` of Proposition 2 (p.15). -/
noncomputable def tilted {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ) (c : X → ℝ)
    (α : ℝ) : Matrix X X ℝ :=
  Matrix.diagonal (fun x => Real.exp (α * c x)) * Q

/-- `sumPairs f x [y₁, …, yₖ] = f x y₁ + f y₁ y₂ + ⋯ + f yₖ₋₁ yₖ`: the sum of `f` over the
consecutive pairs of the path `x, y₁, …, yₖ`. -/
def sumPairs {X E : Type*} [AddCommMonoid E] (f : X → X → E) : X → List X → E
  | _, [] => 0
  | x, y :: ys => f x y + sumPairs f y ys

/-- `pathProb Q x [y₁, …, yₖ] = Q x y₁ · Q y₁ y₂ ⋯ Q yₖ₋₁ yₖ`: the probability that the chain with
transition matrix `Q` started at `x` follows the path `y₁, …, yₖ`. -/
def pathProb {X : Type*} (Q : Matrix X X ℝ) : X → List X → ℝ
  | _, [] => 1
  | x, y :: ys => Q x y * pathProb Q y ys

/-- An **excursion** avoiding `xstar` is a finite list of states different from `xstar`. Started at
`x`, the list `l` stands for the trajectory `Φ₀ = x`, `Φᵢ = l[i-1]` for `1 ≤ i < τ`, `Φ_τ = xstar`,
where `τ = l.length + 1` is the first return time `τ_{x*} := inf{i ∈ ℕ : Φᵢ = x*}` (p.4, p.17), with
`ℕ` the strictly positive integers. In particular `τ ≥ 1` also when `x = xstar`.

**Formalization Note** The excursions enumerate the values of the first-passage trajectory on
`{τ_{x*} < ∞}`. Under Assumption 1 this event has probability one, so expectations over excursions
are the expectations of the paper. -/
abbrev Excursion {X : Type*} (xstar : X) : Type _ :=
  {l : List X // ∀ y ∈ l, y ≠ xstar}

/-- The first return time `τ_{x*}` of the trajectory coded by the list `l`. -/
def returnTime {X : Type*} (l : List X) : ℕ :=
  l.length + 1

/-- The probability under `Q` from `x` of the trajectory `x, l, xstar`: the product of `Q` over the
`τ = l.length + 1` transitions, including the last one into `xstar`. -/
def excursionProb {X : Type*} (Q : Matrix X X ℝ) (xstar x : X) (l : List X) : ℝ :=
  pathProb Q x (l ++ [xstar])

/-- The expectation `E^Q_{Φ₀ = x}[f]` of a `[0, ∞]`-valued function of the excursion to `xstar`.

**Formalization Note** The value lies in `ℝ≥0∞`, so an infinite expectation is `⊤`, not the value
`0` of a real `∑'` over a non-summable family. -/
noncomputable def excursionExp {X : Type*} (Q : Matrix X X ℝ) (xstar x : X)
    (f : List X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' l : Excursion xstar, ENNReal.ofReal (excursionProb Q xstar x l) * f l

/-- The vector-valued expectation `E^Q_{Φ₀ = x}[f]` of a function of the excursion to `xstar`.

**Formalization Note** This is a real `∑'`, which is `0` for a non-summable family, so every
statement using it also asserts `excursionSummable`. -/
noncomputable def excursionMean {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Matrix X X ℝ) (xstar x : X) (f : List X → E) : E :=
  ∑' l : Excursion xstar, excursionProb Q xstar x l • f l

/-- The family defining `excursionMean Q xstar x f` is summable. -/
def excursionSummable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Matrix X X ℝ) (xstar x : X) (f : List X → E) : Prop :=
  Summable fun l : Excursion xstar => excursionProb Q xstar x l • f l

/-- The sum `Σ_{i=0}^{τ-1} (α c(Φᵢ) - Λ)` along the excursion `l` from `x`: the `τ` states
`Φ₀ = x, …, Φ_{τ-1}` count, and `xstar` at time `τ` does not. -/
noncomputable def excursionCost {X : Type*} (c : X → ℝ) (α Λ : ℝ) (x : X) (l : List X) : ℝ :=
  ((x :: l).map fun y => α * c y - Λ).sum

/-- `E^Q_{Φ₀ = x}[exp(Σ_{i=0}^{τ_{x*}-1} (α c(Φᵢ) - Λ))]`, the function of Corollary 1 (p.17), with
values in `[0, ∞]` (it is `+∞` for small `Λ`, p.4). -/
noncomputable def cycleMgf {X : Type*} (Q : Matrix X X ℝ) (c : X → ℝ) (α : ℝ) (xstar : X) (Λ : ℝ)
    (x : X) : ℝ≥0∞ :=
  excursionExp Q xstar x fun l => ENNReal.ofReal (Real.exp (excursionCost c α Λ x l))

/-- `E^Q_{Φ₀ = x}[R^{τ_{x*}}]`, the quantity of Lemma 1 (p.22), in `[0, ∞]`. -/
noncomputable def returnMoment {X : Type*} (Q : Matrix X X ℝ) (xstar x : X) (R : ℝ) : ℝ≥0∞ :=
  excursionExp Q xstar x fun l => ENNReal.ofReal (R ^ returnTime l)

/-- The conclusion of Lemma 1 (p.22) for a set `S` of transition matrices: there is
`R̄ > 1` such that for any `R ∈ (1, R̄)` there are `m(R), M(R) ∈ (1, ∞)` with
`m(R) < E^Q_{Φ₀ = x}[R^{τ_{x*}}] < M(R)` for all `Q ∈ S` and `x`, and moreover `M(R) ↓ 1` as `R ↓ 1`.

The constants come first and do not depend on `Q` or `x`. "`M(R) ↓ 1` as `R ↓ 1`" is the monotonicity
of `M` on `(1, R̄)` together with the limit from the right at `1`. Corollary 4 (p.23), "Lemma 1 holds
for" the closure of the twisted kernels, is this same predicate for another set. -/
def UniformReturnMoments {X : Type*} (S : Set (Matrix X X ℝ)) (xstar : X) : Prop :=
  ∃ Rbar : ℝ, 1 < Rbar ∧ ∃ mLow mUp : ℝ → ℝ,
    (∀ R, 1 < R → R < Rbar → 1 < mLow R ∧ 1 < mUp R ∧
      ∀ Q ∈ S, ∀ x,
        ENNReal.ofReal (mLow R) < returnMoment Q xstar x R ∧
          returnMoment Q xstar x R < ENNReal.ofReal (mUp R)) ∧
    MonotoneOn mUp (Set.Ioo 1 Rbar) ∧ Tendsto mUp (𝓝[>] 1) (𝓝 1)

end RiskExpPG


