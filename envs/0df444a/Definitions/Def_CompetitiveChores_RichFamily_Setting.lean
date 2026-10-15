-- Prove2me | Definitions.Def_CompetitiveChores_RichFamily_Setting
-- name    : CompetitiveChores_RichFamily_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:05.651858+00:00
-- url     : https://prove2.me/theorems/e42264a8-1949-46e2-8adc-36ac26e32159
-- title:
--   pp. 10–16 — chore division problem, feasible allocations, utilities, competitive allocations (Definition 3), Pareto optimality (Definition 5), Pareto frontier and its faces
-- statement:
--   This file fixes the model of competitive division of divisible chores of Brânzei and Sandomirskiy.
--
--   **Agents, chores, allocations.** There are $n$ agents and $m$ divisible chores, one unit of each. A *bundle* is a vector $x\in\mathbb R^m_{\ge 0}$, where $x_j$ is the amount of chore $j$. An *allocation* $z=(z_i)_{i\in[n]}$ gives agent $i$ the bundle $z_i$; it is *feasible* if $z\ge 0$ and all chores are distributed:
--   $$\sum_{i=1}^n z_{i,j}=1\qquad\text{for each chore } j.$$
--
--   **Utilities.** Values are given by a matrix $v$ (in the theorems $v\in\mathbb R^{n\times m}_{<0}$: chores are bads). The utility of agent $i$ for a bundle $x$ is $u_i(x)=\sum_{j=1}^m v_{i,j}x_j$, the *utility profile* of an allocation $z$ is $u(z)=(u_1(z_1),\dots,u_n(z_n))$, and
--   $$\mathcal U(v)=\{w\in\mathbb R^n : w=u(z)\text{ for some feasible allocation } z\}$$
--   is the set of feasible utility profiles.
--
--   **Competitive allocations (Definition 3).** For prices $p\in\mathbb R^m$ the price of a bundle is $p(x)=\sum_j p_jx_j$. Given budgets $b\in\mathbb R^n$ (in the theorems $b\in\mathbb R^n_{<0}$), a feasible allocation $z$ is *competitive at prices* $p$ if $p\in\mathbb R^m_{<0}$ and, for each agent $i$, the bundle $z_i$ is within her budget, $p(z_i)\le b_i$, and maximizes her utility among all bundles within her budget:
--   $$u_i(z_i)\ge u_i(x)\qquad\text{for every } x\in\mathbb R^m_{\ge0}\text{ with } p(x)\le b_i.$$
--   $z$ is *competitive* if it is competitive at some prices, and $u$ is a *competitive utility profile* if $u=u(z)$ for some competitive allocation $z$.
--
--   **Pareto optimality (Definition 5).** A feasible allocation $z$ is *Pareto optimal* if there is no feasible $z'$ with $u_i(z'_i)\ge u_i(z_i)$ for every agent and strict inequality for at least one. The *Pareto frontier* $\mathcal U^*(v)$ is the set of feasible profiles $w\in\mathcal U(v)$ such that every $w'\in\mathcal U(v)$ with $w'\ge w$ equals $w$; these are exactly the utility profiles of Pareto optimal allocations.
--
--   **Faces of the Pareto frontier (p. 16).** For weights $\tau\in\mathbb R^n$ the face exposed by $\tau$ is the set of maximizers of the linear form $\langle\tau,u\rangle=\sum_i\tau_iu_i$ over $u\in\mathcal U(v)$. The *faces of the Pareto frontier* are the faces exposed by strictly positive weights $\tau\in\mathbb R^n_{>0}$.
--
--   These objects are the vocabulary of every statement of the mission: the competitive rule, the welfare theorems, and the counting of faces and competitive profiles.
--
--   **Formalization Note** Agents are `Fin n` and chores `Fin m`, numbered from 0. Values, budgets and prices are real functions; the sign conditions $v<0$, $b<0$ are hypotheses of the theorems, while $p<0$ is part of the definition of a competitive allocation. Definition 3 is encoded with the budget constraint $p(z_i)\le b_i$ written out, as the phrase "maximizes her utility among all bundles within her budget" requires. A face is represented by the set of maximizers itself (the paper's dual representation of a face, p. 16), and "faces of the Pareto frontier" are those exposed by $\tau\in\mathbb R^n_{>0}$, as in the proof of Lemma 18 (p. 21).
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, pp. 10–11 (§2, Definitions 2, 3, 5), p. 2 (List of Symbols, 𝒰*(v)), p. 16 (§2.4, faces), p. 21 (proof of Lemma 18)

import Mathlib

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- p. 10: an allocation `z` (agent `i` receives the bundle `z i`, `z i j` is the amount of chore `j`)
is feasible if `z ≥ 0` and every chore is fully distributed: `∑_i z_{i,j} = 1` for each chore `j`. -/
def IsFeasible (z : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ z i j) ∧ ∀ j, ∑ i, z i j = 1

/-- p. 10: the additive utility `u_i(x) = ∑_j v_{i,j} x_j` of agent `i` for the bundle `x`. -/
def bundleUtility (v : Fin n → Fin m → ℝ) (i : Fin n) (x : Fin m → ℝ) : ℝ :=
  ∑ j, v i j * x j

/-- p. 10: the utility profile `u(z) = (u_1(z_1), …, u_n(z_n))` of an allocation `z`. -/
def utilityProfile (v : Fin n → Fin m → ℝ) (z : Fin n → Fin m → ℝ) : Fin n → ℝ :=
  fun i => bundleUtility v i (z i)

/-- p. 10: `𝒰(v)`, the set of utility profiles of feasible allocations. -/
def feasibleUtilities (v : Fin n → Fin m → ℝ) : Set (Fin n → ℝ) :=
  {w | ∃ z, IsFeasible z ∧ utilityProfile v z = w}

/-- §2.1, p. 10: the price `p(x) = ∑_j p_j x_j` of the bundle `x` at prices `p`. -/
def bundlePrice (p : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ j, p j * x j

/-- Definition 3, pp. 10–11: the feasible allocation `z` is competitive for the problem `(v, b)` at the
strictly negative prices `p` if, for each agent `i`, the bundle `z i` is within her budget,
`p(z_i) ≤ b_i`, and maximizes her utility among all bundles `x ≥ 0` with `p(x) ≤ b_i`. -/
def IsCompetitiveWith (v : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (z : Fin n → Fin m → ℝ)
    (p : Fin m → ℝ) : Prop :=
  IsFeasible z ∧ (∀ j, p j < 0) ∧ ∀ i, bundlePrice p (z i) ≤ b i ∧
    ∀ x : Fin m → ℝ, (∀ j, 0 ≤ x j) → bundlePrice p x ≤ b i →
      bundleUtility v i x ≤ bundleUtility v i (z i)

/-- Definition 3: `z` is competitive if it is competitive at some vector of prices. -/
def IsCompetitive (v : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (z : Fin n → Fin m → ℝ) : Prop :=
  ∃ p, IsCompetitiveWith v b z p

/-- p. 14, p. 18 ff.: a competitive utility profile is the utility profile of a competitive allocation. -/
def IsCompetitiveProfile (v : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (u : Fin n → ℝ) : Prop :=
  ∃ z, IsCompetitive v b z ∧ utilityProfile v z = u

/-- Definition 5, p. 11: `z` is Pareto optimal if it is feasible and no feasible `z'` gives every agent
at least as much utility and some agent strictly more. -/
def IsParetoOptimal (v : Fin n → Fin m → ℝ) (z : Fin n → Fin m → ℝ) : Prop :=
  IsFeasible z ∧ ¬ ∃ z', IsFeasible z' ∧
    (∀ i, utilityProfile v z i ≤ utilityProfile v z' i) ∧
      ∃ i, utilityProfile v z i < utilityProfile v z' i

/-- Definition 5, p. 11 (and List of Symbols, p. 2): the Pareto frontier `𝒰*(v)`, the feasible utility
profiles not weakly dominated by another feasible profile. -/
def paretoFrontier (v : Fin n → Fin m → ℝ) : Set (Fin n → ℝ) :=
  {w | w ∈ feasibleUtilities v ∧ ∀ w' ∈ feasibleUtilities v, (∀ i, w i ≤ w' i) → w' = w}

/-- p. 16: the face of `𝒰(v)` exposed by the weight vector `τ`: the maximizers of the linear form
`⟨τ, u⟩ = ∑_i τ_i u_i` over `u ∈ 𝒰(v)`. -/
def paretoFace (v : Fin n → Fin m → ℝ) (τ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | u ∈ feasibleUtilities v ∧ ∀ w ∈ feasibleUtilities v, ∑ i, τ i * w i ≤ ∑ i, τ i * u i}

/-- p. 16 and proof of Lemma 18, p. 21: the faces of the Pareto frontier are the faces `paretoFace v τ`
exposed by strictly positive weights `τ ∈ ℝ^n_{>0}`. -/
def paretoFaces (v : Fin n → Fin m → ℝ) : Set (Set (Fin n → ℝ)) :=
  {f | ∃ τ : Fin n → ℝ, (∀ i, 0 < τ i) ∧ f = paretoFace v τ}

end CompetitiveChores.RichFamily


