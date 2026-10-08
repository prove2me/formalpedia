-- Prove2me | Definitions.Def_SPHardness_IntFeas_Model
-- name    : SPHardness_IntFeas_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:57.265918+00:00
-- url     : https://prove2.me/theorems/5361cd76-5633-4a7a-93c1-c6bb69a6177f
-- title:
--   §2–§3, pp. 8, 12–13 — the Integer Feasibility Problem, the random-recourse program (11), its feasibility, objective, optimal value f⋆, ϵ-optimality and x⋆
-- statement:
--   This file fixes the objects of the second hardness result for random recourse in Hanasusanto, Kuhn and Wiesemann.
--
--   **The Integer Feasibility Problem.** An instance consists of an integer matrix $A\in\mathbb Z^{m\times n}$ and an integer vector $b\in\mathbb Z^m$ such that
--   $$\{y\in\mathbb R^n : Ay\le b\}\subseteq[0,1]^n .$$
--   The question is whether there is a binary vector $y\in\{0,1\}^n$ with $Ay\le b$. We write $\mathrm{IFP}(A,b)$ for the statement that the answer is affirmative, and $P(A,b)=\{\xi\in\mathbb R^n : A\xi\le b\}$ for the polytope.
--
--   **The second-stage problem.** Let $\xi\in[0,1]^n$ be a realization of the uncertain parameter and $x\in\mathbb R$ a first-stage decision. Write $s(\xi)=b-A\xi\in\mathbb R^m$ for the slack vector. A pair $(y,\lambda)\in\mathbb R^n\times\mathbb R^m$ is *second-stage feasible* if
--   1. $y\ge 0$ and $\lambda\ge 0$;
--   2. $x\ge e^\top y=\sum_i y_i$;
--   3. for every $i=1,\dots,n$: $y_i\ge \xi_i+s(\xi)^\top\lambda$ and $y_i\ge (1-\xi_i)+s(\xi)^\top\lambda$.
--
--   The recourse function $Q(x,\xi)$ is the optimal value $\inf\{e^\top y : (y,\lambda)\text{ second-stage feasible}\}$.
--
--   **Problem (11).** With $\tilde\xi$ uniformly distributed on $[0,1]^n$, problem (11) is
--   $$\text{minimize } x+\mathbb E\big[Q(x,\tilde\xi)\big]\quad\text{subject to } x\in\mathbb R .$$
--   A decision $x$ is *feasible* when the second-stage problem is feasible for every $\xi\in[0,1]^n$. The optimal value $f^\star$ is the infimum of the objective over feasible $x$, and a feasible $x$ is *$\epsilon$-optimal* if
--   $$\frac{\big|f^\star-\big(x+\mathbb E[Q(x,\tilde\xi)]\big)\big|}{\max\{|f^\star|,1\}}\le\epsilon .$$
--   Finally,
--   $$x^\star=\max\Big\{\sum_{i=1}^n\max\{\xi_i,1-\xi_i\} : A\xi\le b\Big\}$$
--   is the value the paper identifies as the optimal decision of (11).
--
--   These objects are shared by every statement of the mission: Lemma 4 (rounding near-binary solutions), the explicit solution of the second stage, the optimality of $x^\star$, and Theorem 4.
--
--   **Formalization Note.** Vectors are functions on `Fin n` / `Fin m`; $A$ and $b$ stay integer and are cast to $\mathbb R$. The uniform law on $[0,1]^n$ is Lebesgue measure restricted to the cube `cube n`, which has volume $1$, so $\mathbb E[Q(x,\tilde\xi)]$ is the set integral `∫ ξ in cube n, secondStageValue A b x ξ`. The constraint block of the second stage is indexed by $i=1,\dots,n$; the page prints "$\forall i=1,\dots,m$" and $\sum_{i=1}^m$ in $x^\star$ together with "$n=m=k$"; the reading here keeps $m$ (the number of rows of $A$) arbitrary and $\xi\in[0,1]^n$, which is the reading under which the proof's $y_i(\xi)=\max\{\xi_i,1-\xi_i\}$, $i=1,\dots,n$, is right for every instance. First-stage feasibility is *robust* (feasible for every $\xi$ in the support): the page says $x$ is infeasible when the second stage is infeasible "with positive probability", but under the almost-every-$\xi$ reading the printed $x^\star$ is wrong whenever $P(A,b)$ is Lebesgue-null, a typical IFP situation. `secondStageValue`, `optValue` and `xStar` are `sInf`/`sSup` in $\mathbb R$; their junk value $0$ on an empty or unbounded set never matters: $Q(x,\xi)$ is only used where the second stage is feasible (its values are bounded below by $0$), `optValue` ranges over feasible $x$ only (a nonempty set on which the objective is bounded below once the instance is nonempty), and `xStar` is a supremum over the polytope, which is bounded (inside $[0,1]^n$) and is assumed nonempty wherever `xStar` is used. When $P(A,b)=\emptyset$, `xStar` is $0$.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 8 (definition of ϵ-optimality), p. 12 (Integer Feasibility Problem), pp. 12–13 (problem (11)), p. 13 (proof of Theorem 4, x⋆)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

open MeasureTheory

namespace SPHardness.IntFeas

variable {m n : ℕ}

/-- The instance condition of the Integer Feasibility Problem (p. 12):
`{y ∈ ℝⁿ : Ay ≤ b} ⊆ [0, 1]ⁿ`. -/
def IsIFPInstance (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Prop :=
  ∀ y : Fin n → ℝ, (∀ i, ∑ j, (A i j : ℝ) * y j ≤ (b i : ℝ)) → ∀ j, 0 ≤ y j ∧ y j ≤ 1

/-- The real vector `ξ` satisfies `Aξ ≤ b`. -/
def InPolytope (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (ξ : Fin n → ℝ) : Prop :=
  ∀ i, ∑ j, (A i j : ℝ) * ξ j ≤ (b i : ℝ)

/-- The question of the Integer Feasibility Problem (p. 12): is there `y ∈ {0, 1}ⁿ` with
`Ay ≤ b`? -/
def IFPAnswer (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Prop :=
  ∃ y : Fin n → ℝ, (∀ j, y j = 0 ∨ y j = 1) ∧ InPolytope A b y

/-- The slack `(b − Aξ)_r` of row `r`. -/
def slack (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (ξ : Fin n → ℝ) (r : Fin m) : ℝ :=
  (b r : ℝ) - ∑ j, (A r j : ℝ) * ξ j

/-- Feasibility of `(y, λ)` in the second-stage problem of (11) for decision `x` and
realization `ξ`: `y ≥ 0`, `λ ≥ 0`, `x ≥ e⊤y`, and for every `i = 1, …, n`,
`yᵢ ≥ ξᵢ + (b − Aξ)⊤λ` and `yᵢ ≥ (1 − ξᵢ) + (b − Aξ)⊤λ`. -/
def SecondStageFeasible (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ)
    (ξ : Fin n → ℝ) (y : Fin n → ℝ) (lam : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ r, 0 ≤ lam r) ∧ ∑ i, y i ≤ x ∧
    ∀ i : Fin n, ξ i + ∑ r, slack A b ξ r * lam r ≤ y i ∧
      (1 - ξ i) + ∑ r, slack A b ξ r * lam r ≤ y i

/-- The second-stage problem of (11) has a feasible solution. -/
def SecondStageSolvable (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ)
    (ξ : Fin n → ℝ) : Prop :=
  ∃ y lam, SecondStageFeasible A b x ξ y lam

/-- The recourse function `Q(x, ξ)`: the optimal value `inf e⊤y` of the second-stage problem.
Meaningful only when `SecondStageSolvable A b x ξ` holds (otherwise it is the junk `sInf ∅ = 0`). -/
noncomputable def secondStageValue (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  sInf {v | ∃ y lam, SecondStageFeasible A b x ξ y lam ∧ v = ∑ i, y i}

/-- First-stage feasibility of `x` in (11): the second stage is feasible for every
realization `ξ ∈ [0, 1]ⁿ` (robust reading). -/
def FirstStageFeasible (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ) : Prop :=
  ∀ ξ ∈ SPHardness.FixedRecourse.cube n, SecondStageSolvable A b x ξ

/-- The objective `x + E[Q(x, ξ̃)]` of (11), with `ξ̃` uniform on `[0, 1]ⁿ`. -/
noncomputable def objective (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : ℝ) : ℝ :=
  x + ∫ ξ in SPHardness.FixedRecourse.cube n, secondStageValue A b x ξ

/-- The optimal value `f⋆` of (11): the infimum of the objective over feasible `x`. -/
noncomputable def optValue (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : ℝ :=
  sInf (objective A b '' {x | FirstStageFeasible A b x})

/-- `x` is an `ε`-optimal decision of (11) (p. 8): `x` is feasible and
`|f⋆ − (x + E[Q(x, ξ̃)])| / max{|f⋆|, 1} ≤ ε`. -/
def IsEpsOptimal (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (ε x : ℝ) : Prop :=
  FirstStageFeasible A b x ∧
    |optValue A b - objective A b x| / max |optValue A b| 1 ≤ ε

/-- The printed value `x⋆ = max{Σᵢ max{ξᵢ, 1 − ξᵢ} : Aξ ≤ b}` (p. 13). -/
noncomputable def xStar (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : ℝ :=
  sSup {v | ∃ ξ : Fin n → ℝ, InPolytope A b ξ ∧ v = ∑ i, max (ξ i) (1 - ξ i)}

end SPHardness.IntFeas


