-- Prove2me | Definitions.Def_ZeroOneSimplex_LPData_IsPivot
-- name    : ZeroOneSimplex_LPData_IsPivot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:42.810002+00:00
-- url     : https://prove2.me/theorems/dc403285-d9c4-4b85-82ea-1157f9527094
-- title:
--   Pivot directions, pivots, optimal bases, the basic cone and the slope condition
-- statement:
--   Let $B$ be a feasible basis with basic solution $x'$.
--
--   1. The **pivot direction** of a nonbasic column $j$ is the unique $w$ with $A'w=0$, $w_j=1$ and $w_k=0$ for every other nonbasic $k$; its original part $z_j$ generates an extreme ray of the basic cone, and $c^\top z_j$ is the reduced cost of $j$.
--   2. $B$ is **optimal** when every reduced cost $c^\top z_j$ is $\le 0$.
--   3. A **pivot** with entering $j$ and leaving $\ell\in B$ requires $w_\ell<0$ and that $\ell$ attain the ratio test $\min\{x'_k/(-w_k): k\in B,\ w_k<0\}$; the new basis is $B-\ell+j$. It is **degenerate** when the vertex does not change.
--   4. The **basic cone** is $\mathcal C(B)=\{z: Az=0,\ z_i\ge0 \text{ for nonbasic original } i,\ D_rz\le 0 \text{ for rows } r \text{ with nonbasic slack}\}$.
--   5. $B$ satisfies the **slope condition** for $v$ if for each $z\in\mathcal C(B)$, $c^\top z>0$ implies $v^\top z>0$.
--   6. $j$ is a **Shadow entering choice** if $c^\top z_j>0$ and $z_j$ maximizes $c^\top z/v^\top z$ among the improving pivot directions.
--
--   **Formalization Note** The pivot direction is defined by $A'w=0$: the printed formula $z'^j(B)=A_B'^{-1}A'_j$ (pp.7, 11) has the wrong sign. The slope condition is on the whole cone, as in the statements of Theorem 7 and Lemma 6.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, §1.1.1, p.7 (pivots, ratio test (2), degenerate pivots); §2, p.8 (basic cone); Theorem 7, p.23; Lemma 6, p.24

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData_basicSol

set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

namespace LPData

variable {n m p : ℕ} (L : LPData n m p)

open Classical in
/-- **Pivot direction** of the nonbasic column `j` for the basis `B` (arXiv:2111.14050v1, p.7):
the unique `w` with `A'w = 0`, `w_j = 1` and `w_k = 0` for every nonbasic `k ≠ j`
(`0` when no unique such `w` exists, never for a basis and `j ∉ B`).

**Formalization Note.** Defining `w` by `A'w = 0` fixes the sign: the printed formula
`z'ʲ(B) = A'_B⁻¹A'_j` (pp.7, 11) has the wrong sign; the basic part of the direction is
`−A'_B⁻¹A'_j`, consistent with the ratio test (2). -/
noncomputable def pivotDir (B : Finset (Fin n ⊕ Fin p)) (j : Fin n ⊕ Fin p) :
    Fin n ⊕ Fin p → ℝ :=
  if h : ∃! w : Fin n ⊕ Fin p → ℝ,
      L.stdA *ᵥ w = 0 ∧ w j = 1 ∧ ∀ k, k ∉ B → k ≠ j → w k = 0 then
    Classical.choose h.exists
  else 0

/-- The original part `z ∈ ℝⁿ` of the pivot direction of `j` (slacks removed): the generator
of an extreme ray of the basic cone `𝒞(B)` (p.8). Its reduced cost is `c̄'(j) = c'ᵀw = cᵀz`. -/
noncomputable def edgeDir (B : Finset (Fin n ⊕ Fin p)) (j : Fin n ⊕ Fin p) : Fin n → ℝ :=
  fun i => L.pivotDir B j (Sum.inl i)

/-- **Optimal basis** (arXiv:2111.14050v1, p.7, Step 1): a feasible basis all of whose reduced
costs `c̄'(j) = cᵀz_j`, `j ∉ B`, are `≤ 0`; the algorithm terminates there. -/
def IsOptimalBasis (B : Finset (Fin n ⊕ Fin p)) : Prop :=
  L.IsFeasibleBasis B ∧ ∀ j, j ∉ B → L.c ⬝ᵥ L.edgeDir B j ≤ 0

/-- **Pivot** (arXiv:2111.14050v1, p.7, Steps 2–4) from the feasible basis `B` with entering
column `j ∉ B` and leaving column `ℓ ∈ B`: with `w` the pivot direction of `j` and `x'` the basic
solution, `w_ℓ < 0` and `ℓ` attains the ratio test
`min {x'_k / (−w_k) : k ∈ B, w_k < 0}` (2); the new basis is `B − ℓ + j`. Ties in the ratio
test may be broken arbitrarily. No condition is put on the reduced cost of `j` here. -/
def IsPivot (B B' : Finset (Fin n ⊕ Fin p)) (j ℓ : Fin n ⊕ Fin p) : Prop :=
  L.IsFeasibleBasis B ∧ j ∉ B ∧ ℓ ∈ B ∧ L.pivotDir B j ℓ < 0 ∧
    (∀ k ∈ B, L.pivotDir B j k < 0 →
      L.basicSol B ℓ / (-L.pivotDir B j ℓ) ≤ L.basicSol B k / (-L.pivotDir B j k)) ∧
    B' = insert j (B.erase ℓ)

/-- **Degenerate pivot** (p.7): a pivot after which the basic feasible solution still
corresponds to the same extreme point (step length `0`). -/
def IsDegeneratePivot (B B' : Finset (Fin n ⊕ Fin p)) : Prop :=
  ∃ j ℓ, L.IsPivot B B' j ℓ ∧ L.vertexOf B' = L.vertexOf B

/-- **Basic cone** of `B` (arXiv:2111.14050v1, §2, p.8): `𝒞(B) = {z ∈ ℝⁿ : Az = 0, D^B z ≤ 0}`,
where `D^B` collects the inequalities that are tight at the vertex because their variable is
nonbasic: `z_i ≥ 0` for each nonbasic original variable `i`, and `D_r z ≤ 0` for each row `r`
whose slack is nonbasic. -/
def basicCone (B : Finset (Fin n ⊕ Fin p)) : Set (Fin n → ℝ) :=
  {z | L.A *ᵥ z = 0 ∧ (∀ i, Sum.inl i ∉ B → 0 ≤ z i) ∧ ∀ r, Sum.inr r ∉ B → (L.D *ᵥ z) r ≤ 0}

/-- **The condition of Theorem 7 and Lemma 6** (arXiv:2111.14050v1, pp.23–24): for each
`z ∈ 𝒞(B)`, if `cᵀz > 0` then `vᵀz > 0`. It is a condition on the whole basic cone, not only
on the pivot directions. -/
def IsReady (B : Finset (Fin n ⊕ Fin p)) (v : Fin n → ℝ) : Prop :=
  ∀ z ∈ L.basicCone B, 0 < L.c ⬝ᵥ z → 0 < v ⬝ᵥ z

/-- **Entering choice of a Shadow pivot rule** (arXiv:2111.14050v1, Theorem 7, p.23): `j` is
nonbasic, its pivot direction `z_j` is improving (`cᵀz_j > 0`), and it maximizes `cᵀz / vᵀz`
among the improving pivot directions of `B`. -/
def IsShadowEntering (B : Finset (Fin n ⊕ Fin p)) (v : Fin n → ℝ) (j : Fin n ⊕ Fin p) : Prop :=
  j ∉ B ∧ 0 < L.c ⬝ᵥ L.edgeDir B j ∧
    ∀ k, k ∉ B → 0 < L.c ⬝ᵥ L.edgeDir B k →
      L.c ⬝ᵥ L.edgeDir B k / v ⬝ᵥ L.edgeDir B k ≤ L.c ⬝ᵥ L.edgeDir B j / v ⬝ᵥ L.edgeDir B j

end LPData

end ZeroOneSimplex


