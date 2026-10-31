-- Prove2me | Definitions.Def_PopularMixed_MixedLP
-- name    : PopularMixed_MixedLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:38.994759+00:00
-- url     : https://prove2.me/theorems/78b7a164-ce74-4448-8eee-9dfb435903e2
-- title:
--   A linear program in general form and its dual
-- statement:
--   A **linear program in general form** with variables $z\in\mathbb R^V$ is
--   $$\min\ \sum_k c_kz_k\quad\text{s.t.}\quad \sum_kP_{ik}z_k\ge p_i\ (i\in I),\qquad \sum_kQ_{jk}z_k=q_j\ (j\in J),\qquad z_k\ge0\ (k\in K),$$
--   the variables outside $K$ being free. Its **dual** is
--   $$\max\ \sum_ip_iy_i+\sum_jq_j\mu_j\quad\text{s.t.}\quad y\ge0,\ \mu\ \text{free},\quad \sum_iP_{ik}y_i+\sum_jQ_{jk}\mu_j\ \begin{cases}\le c_k & k\in K\\ =c_k & k\notin K.\end{cases}$$
--
--   This is the textbook primal–dual pair; it is used to state the self-duality of LP2 (Lemma 2.1) without writing its dual LP3 by hand.
--
--   **Formalization Note** `MixedLP V I J` stores $c,P,p,Q,q$ and the predicate `nonneg` ($k\in K$); `Feasible`, `objective`, `DualFeasible`, `dualObjective`, `IsOptimal`, `IsDualOptimal` are as displayed.
-- source:
--   Standard linear programming duality, used for Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 2.1, PDF pp.5–6 (the dual LP3 of LP2).

import Mathlib

namespace PopularMixed

/-!
A linear program in general (mixed) form and its Lagrangian dual, the textbook primal–dual pair
used to state the self-duality of LP2 (Huang–Kavitha, *Popularity, Mixed Matchings, and
Self-duality*, conference version (SODA 2017), Lemma 2.1, PDF p.5).

The primal is
  minimize `Σ_k c_k z_k` over `z : V → ℝ`
  subject to `Σ_k P_{ik} z_k ≥ p_i` (`i ∈ I`), `Σ_k Q_{jk} z_k = q_j` (`j ∈ J`),
  `z_k ≥ 0` for the sign-constrained variables `k` (`nonneg k`), `z_k` free otherwise.
Its dual is
  maximize `Σ_i p_i y_i + Σ_j q_j μ_j` over `y : I → ℝ`, `μ : J → ℝ`
  subject to `y ≥ 0`, `μ` free, and for every variable `k`:
  `Σ_i P_{ik} y_i + Σ_j Q_{jk} μ_j ≤ c_k` if `z_k ≥ 0`, and `= c_k` if `z_k` is free.
-/

/-- A linear program in general form (minimization, `≥` rows, `=` rows, sign-constrained and
free variables). -/
structure MixedLP (V I J : Type*) where
  /-- The cost vector. -/
  c : V → ℝ
  /-- The coefficient matrix of the `≥` rows. -/
  P : I → V → ℝ
  /-- The right-hand side of the `≥` rows. -/
  p : I → ℝ
  /-- The coefficient matrix of the `=` rows. -/
  Q : J → V → ℝ
  /-- The right-hand side of the `=` rows. -/
  q : J → ℝ
  /-- The variables constrained to be nonnegative (the others are free). -/
  nonneg : V → Prop

namespace MixedLP

variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] (L : MixedLP V I J)

/-- The primal objective `Σ_k c_k z_k` (to be minimized). -/
def objective (z : V → ℝ) : ℝ := ∑ k, L.c k * z k

/-- Primal feasibility. -/
def Feasible (z : V → ℝ) : Prop :=
  (∀ i, L.p i ≤ ∑ k, L.P i k * z k) ∧ (∀ j, ∑ k, L.Q j k * z k = L.q j) ∧
    ∀ k, L.nonneg k → 0 ≤ z k

/-- An optimal primal solution. -/
def IsOptimal (z : V → ℝ) : Prop :=
  L.Feasible z ∧ ∀ z', L.Feasible z' → L.objective z ≤ L.objective z'

/-- The dual objective `Σ_i p_i y_i + Σ_j q_j μ_j` (to be maximized). -/
def dualObjective (y : I → ℝ) (μ : J → ℝ) : ℝ :=
  (∑ i, L.p i * y i) + ∑ j, L.q j * μ j

/-- Dual feasibility: `y ≥ 0`, `μ` free, and for every primal variable `k` the dual constraint
`Σ_i P_{ik} y_i + Σ_j Q_{jk} μ_j ≤ c_k` (if `z_k ≥ 0`) or `= c_k` (if `z_k` is free). -/
def DualFeasible (y : I → ℝ) (μ : J → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧
    ∀ k, (L.nonneg k → (∑ i, L.P i k * y i) + (∑ j, L.Q j k * μ j) ≤ L.c k) ∧
      (¬ L.nonneg k → (∑ i, L.P i k * y i) + (∑ j, L.Q j k * μ j) = L.c k)

/-- An optimal dual solution. -/
def IsDualOptimal (y : I → ℝ) (μ : J → ℝ) : Prop :=
  L.DualFeasible y μ ∧ ∀ y' μ', L.DualFeasible y' μ' → L.dualObjective y' μ' ≤ L.dualObjective y μ

end MixedLP

end PopularMixed


