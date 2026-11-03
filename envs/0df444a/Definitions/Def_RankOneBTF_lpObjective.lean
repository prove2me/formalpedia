-- Prove2me | Definitions.Def_RankOneBTF_lpObjective
-- name    : RankOneBTF_lpObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:05.911936+00:00
-- url     : https://prove2.me/theorems/3645de59-d37b-4975-8aa3-5eaf95ea27ef
-- title:
--   The objective of (extP), LP points $(x,y,z,\mathcal W)$, optimal and unique optimal solutions
-- statement:
--   The LP relaxations of rank-one Boolean tensor factorization have variables $(x,y,z,\mathcal W)\in\mathbb R^n\times\mathbb R^m\times\mathbb R^l\times\mathbb R^{n\times m\times l}$. For an input tensor $\mathcal G$ let
--   $$
--   S_0=\{(i,j,k): g_{ijk}=0\},\qquad S_1=\{(i,j,k): g_{ijk}=1\}.
--   $$
--   All problems share the objective of Problem (extP),
--   $$
--   \sum_{(i,j,k)\in S_0} w_{ijk}+\sum_{(i,j,k)\in S_1}(1-w_{ijk}).
--   $$
--   The **ground truth point** is $(\bar x,\bar y,\bar z,\bar{\mathcal W})$ with $\bar{\mathcal W}=\bar x\otimes\bar y\otimes\bar z$, read as a $\{0,1\}$-valued real point.
--
--   A feasible point $v$ of a minimization problem $\min\{f(u):u\in S\}$ is an **optimal solution** if $f(v)\le f(u)$ for all $u\in S$, and the **unique optimal solution** if moreover every $u\in S$ with $f(u)\le f(v)$ equals $v$. An optimization problem **recovers the ground truth** if it has a unique optimal solution and it is the ground truth.
--
--   **Formalization Note** The objective is defined on the tensor part $\mathcal W$ alone (`objW`) and lifted to LP points (`lpObjective`); uniqueness is phrased as "every feasible point with objective at most $f(v)$ equals $v$".
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, p.2 (Problem (extP), sets S0, S1 (1)), p.3 (recovery: unique optimal solution equal to the ground truth)

import Mathlib
import Definitions.Def_RankOneBTF_groundTruth

namespace RankOneBTF

/-- A point `(x, y, z, W) ∈ ℝⁿ × ℝᵐ × ℝˡ × ℝ^{n×m×l}`: the variables of the LP relaxations
(sLP) and (fLP) of rank-one BTF (arXiv:2202.07053v3, §3, pp.6–8). -/
abbrev LPPoint (n m l : ℕ) : Type :=
  (Fin n → ℝ) × (Fin m → ℝ) × (Fin l → ℝ) × (Fin n → Fin m → Fin l → ℝ)

/-- A binary vector read as a `{0,1}`-valued real vector (`true ↦ 1`, `false ↦ 0`). -/
def realVec {n : ℕ} (v : Fin n → Bool) : Fin n → ℝ := fun i => if v i then 1 else 0

/-- A binary tensor read as a `{0,1}`-valued real tensor (`true ↦ 1`, `false ↦ 0`). -/
def realTensor {n m l : ℕ} (W : BTensor n m l) : Fin n → Fin m → Fin l → ℝ :=
  fun i j k => if W i j k then 1 else 0

/-- The ground truth point `(x̄, ȳ, z̄, W̄)` with `W̄ = x̄ ⊗ ȳ ⊗ z̄` (arXiv:2202.07053v3, p.3),
as a point of the LP variable space. -/
def groundPoint {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) :
    LPPoint n m l :=
  (realVec xb, realVec yb, realVec zb, realTensor (groundTruth xb yb zb))

/-- The objective of Problem (extP) (arXiv:2202.07053v3, §1, p.2), shared by (sLP) and (fLP):
`Σ_{(i,j,k)∈S₀} w_ijk + Σ_{(i,j,k)∈S₁} (1 − w_ijk)`, where
`S₀ = {(i,j,k) : g_ijk = 0}` and `S₁ = {(i,j,k) : g_ijk = 1}` (1) for the input tensor `G`. -/
def objW {n m l : ℕ} (G : BTensor n m l) (W : Fin n → Fin m → Fin l → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if G i j k then 1 - W i j k else W i j k

/-- The objective `objW G W` evaluated at an LP point `(x, y, z, W)`. -/
def lpObjective {n m l : ℕ} (G : BTensor n m l) (pt : LPPoint n m l) : ℝ :=
  objW G pt.2.2.2

/-- `v` is an **optimal solution** of `min {f u : u ∈ S}`: it is feasible and no feasible point
has a smaller objective value. -/
def IsOptimalOn {V : Type*} (S : Set V) (f : V → ℝ) (v : V) : Prop :=
  v ∈ S ∧ ∀ u ∈ S, f v ≤ f u

/-- `v` is the **unique optimal solution** of `min {f u : u ∈ S}`: it is feasible and every
feasible point whose objective value is at most `f v` equals `v` (so `v` is optimal and no
other point is). An optimization problem **recovers the ground truth** if its unique optimal
solution is the ground truth (arXiv:2202.07053v3, §1, p.3). -/
def IsUniqueOptimalOn {V : Type*} (S : Set V) (f : V → ℝ) (v : V) : Prop :=
  v ∈ S ∧ ∀ u ∈ S, f u ≤ f v → u = v

end RankOneBTF


