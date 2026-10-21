-- Prove2me | Definitions.Def_YeIPA_Geometry_CentralPath
-- name    : YeIPA_Geometry_CentralPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:20.571974+00:00
-- url     : https://prove2.me/theorems/2e8f7b01-a155-49c9-a405-23d17bafeb77
-- title:
--   Standard-form LP $(LP)$/$(LD)$, the central path, the strict complementarity partition $(P^*, Z^*)$, the analytic centers of the optimal faces and the neighbourhood $\mathcal N(\eta)$
-- statement:
--   Fix a real $m\times n$ matrix $A$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$. Ye's standard-form linear program and its dual are
--   $$(LP)\quad \min\ c^Tx\ \text{ s.t. } Ax=b,\ x\ge 0,\qquad\qquad (LD)\quad \max\ b^Ty\ \text{ s.t. } A^Ty+s=c,\ s\ge 0 .$$
--   Vector inequalities are componentwise. This module defines:
--
--   1. **Feasible** and **interior feasible** points: $x$ with $Ax=b$, $x\ge0$ (resp. $x>0$); $(y,s)$ with $A^Ty+s=c$, $s\ge 0$ (resp. $s>0$).
--   2. **Optimal solutions**: a feasible $x$ with $c^Tx\le c^Tx'$ for every feasible $x'$; a feasible $(y,s)$ with $b^Ty'\le b^Ty$ for every feasible $(y',s')$.
--   3. **Central path points** with parameter $\mu$: triples $(x,y,s)$ with $x$ and $(y,s)$ interior feasible and $Xs=\mu e$, that is $x_js_j=\mu$ for every $j$ (system (2.18), p. 70).
--   4. **Strictly complementary pairs**: feasible $x$ and $(y,s)$ with $x_js_j=0$ and $x_j+s_j>0$ for every $j$ (Theorem 1.14). The **strict complementarity partition** is $P^*=\{j: x^*_j>0\}$, $Z^*=\{j: s^*_j>0\}$ for such a pair; here $P^*$ (resp. $Z^*$) is the set of indices $j$ with $x_j>0$ (resp. $s_j>0$) for *some* strictly complementary pair, which by Theorem 1.14 is the book's set.
--   5. The **primal optimal face** $\{x : A_{P^*}x_{P^*}=b,\ x_{P^*}\ge0,\ x_{Z^*}=0\}$ and the **dual optimal face** $\{y: c_{Z^*}-A_{Z^*}^Ty\ge0,\ c_{P^*}-A_{P^*}^Ty=0\}$ (p. 21), the latter described by its slack vectors $s=c-A^Ty$, with $s_{Z^*}\ge0$, $s_{P^*}=0$.
--   6. The **analytic center** of the primal optimal face: a point $x$ of the face with $x_{P^*}>0$ that maximizes $\sum_{j\in P^*}\log x'_j$ over the points $x'$ of the face with $x'_{P^*}>0$; likewise the analytic center of the dual optimal face maximizes $\sum_{j\in Z^*}\log s'_j$ over its slacks with $s'_{Z^*}>0$ (p. 72).
--   7. The one-sided "norm" $\|v\|_{-\infty}=|\min(0,\min_j v_j)|$, the centrality parameter $\mu = x^Ts/n$ and, for a size function $\|\cdot\|$ on $\mathbb R^n$, the **neighbourhood of the central path** (p. 73)
--   $$\mathcal N(\eta)=\Big\{(x,y,s) \text{ interior feasible}:\ \|Xs-\mu e\|\le \eta\mu,\ \mu=\tfrac{x^Ts}{n}\Big\}.$$
--
--   These are the objects of Theorems 2.16–2.18 of Ye's Chapter 2.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so indices $1,\dots,n$ become $0,\dots,n-1$; $c^Tx$ is `c ⬝ᵥ x`, $Ax$ is `A *ᵥ x`. Both optimal faces are written for full vectors in $\mathbb R^n$ (the coordinates outside $P^*$, resp. $Z^*$, are zero on the face), and the logarithm is only ever evaluated on strictly positive coordinates. The book writes "‖.‖ can be any norm, or even a one-sided norm" in $\mathcal N(\eta)$; the definition takes the size function `nrm` as a parameter, and the theorems that use it require $\|v\|_{-\infty}\le\|v\|$ for all $v$, which every $\ell_p$ norm and the one-sided norm itself satisfy (finding F5 shows the reading with an arbitrary norm fails). At $n=0$, `negInfNorm` is $0$. No rank condition on $A$ is built in: it is a hypothesis of each theorem.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 18–19 ((LP), (LD)), p. 20 (Theorem 1.14), p. 21 (strict complementarity partition, optimal faces), p. 70 (central path, (2.18)), p. 72 (analytic centers of the optimal faces), p. 73 (N(η))

import Mathlib

open Matrix

namespace YeIPA.Geometry

/-!
# Standard-form LP, its central path, the strict complementarity partition and the
# analytic centers of the optimal faces

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997: (LP) and (LD) pp. 18–19,
strict complementarity and the optimal faces pp. 20–21, the central path p. 70 (2.18),
the neighbourhood `N(η)` p. 73.

`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`. The book's indices
`1, …, n` are `0, …, n-1` here. Vector inequalities are componentwise.
-/

variable {m n : ℕ}

/-- `x` is feasible for (LP) `minimize cᵀx s.t. Ax = b, x ≥ 0` (p. 18): `x ∈ F_p`. -/
def PrimalFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j

/-- `(y, s)` is feasible for (LD) `maximize bᵀy s.t. Aᵀy + s = c, s ≥ 0` (p. 19): `(y, s) ∈ F_d`. -/
def DualFeasible (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 ≤ s j

/-- `x` is an interior feasible point of (LP): `Ax = b` and `x > 0` (every coordinate). -/
def PrimalInterior (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 < x j

/-- `(y, s)` is an interior feasible point of (LD): `Aᵀy + s = c` and `s > 0`. -/
def DualInterior (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 < s j

/-- `x` is an optimal solution of (LP) (p. 19): feasible, and `cᵀx ≤ cᵀx'` for every feasible
`x'`. -/
def IsPrimalOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- `(y, s)` is an optimal solution of (LD): feasible, and `bᵀy' ≤ bᵀy` for every feasible
`(y', s')`. -/
def IsDualOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  DualFeasible A c y s ∧ ∀ y' s', DualFeasible A c y' s' → b ⬝ᵥ y' ≤ b ⬝ᵥ y

/-- `(x, y, s)` is a central path point with parameter `μ` (p. 70, system (2.18)):
`x` and `(y, s)` are interior feasible and `Xs = μe`, i.e. `xⱼ sⱼ = μ` for every `j`. -/
def IsCentralPathPoint (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  PrimalInterior A b x ∧ DualInterior A c y s ∧ ∀ j, x j * s j = μ

/-- `x` and `(y, s)` are a pair of strictly complementary solutions (Theorem 1.14, p. 20):
`x` is feasible for (LP), `(y, s)` is feasible for (LD), `X s = 0` and `x + s > 0`. -/
def IsStrictlyComplementary (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  PrimalFeasible A b x ∧ DualFeasible A c y s ∧ (∀ j, x j * s j = 0) ∧ ∀ j, 0 < x j + s j

/-- `P* = {j : x*ⱼ > 0}` for a strictly complementary pair `(x*, s*)` (Theorem 1.14, p. 20; the
book proves this set is the same for every such pair). Here: the indices `j` with `x*ⱼ > 0` for
some strictly complementary pair. -/
noncomputable def Pstar (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun j => ∃ x y s, IsStrictlyComplementary A b c x y s ∧ 0 < x j)

/-- `Z* = {j : s*ⱼ > 0}` for a strictly complementary pair `(x*, s*)` (Theorem 1.14, p. 20).
Here: the indices `j` with `s*ⱼ > 0` for some strictly complementary pair. -/
noncomputable def Zstar (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun j => ∃ x y s, IsStrictlyComplementary A b c x y s ∧ 0 < s j)

/-- The primal optimal face (p. 21): `{x : A_{P*} x_{P*} = b, x_{P*} ≥ 0, x_{Z*} = 0}`, written
for full vectors `x ∈ ℝⁿ` (so `A_{P*} x_{P*} = Ax` once `x_{Z*} = 0`). -/
def PrimalOptimalFace (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | A *ᵥ x = b ∧ (∀ j ∈ Pstar A b c, 0 ≤ x j) ∧ ∀ j ∈ Zstar A b c, x j = 0}

/-- The dual optimal face (p. 21), `{y : c_{Z*} − A_{Z*}ᵀ y ≥ 0, c_{P*} − A_{P*}ᵀ y = 0}`, written
for slack vectors: the `s` with `s = c − Aᵀy` for some `y`, `s_{Z*} ≥ 0` and `s_{P*} = 0`. -/
def DualOptimalFace (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {s | (∃ y, Aᵀ *ᵥ y + s = c) ∧ (∀ j ∈ Zstar A b c, 0 ≤ s j) ∧ ∀ j ∈ Pstar A b c, s j = 0}

/-- `x` is (the full vector of) the analytic center of the primal optimal face (p. 72):
`x` lies on the face, `x_{P*} > 0`, and `x_{P*}` maximizes `∑_{j ∈ P*} log xⱼ` over the points
`x'` of the face with `x'_{P*} > 0`. -/
def IsPrimalFaceAnalyticCenter (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ PrimalOptimalFace A b c ∧ (∀ j ∈ Pstar A b c, 0 < x j) ∧
    ∀ x' ∈ PrimalOptimalFace A b c, (∀ j ∈ Pstar A b c, 0 < x' j) →
      ∑ j ∈ Pstar A b c, Real.log (x' j) ≤ ∑ j ∈ Pstar A b c, Real.log (x j)

/-- `s` is (the full slack vector of) the analytic center of the dual optimal face (p. 72):
`s` lies on the face, `s_{Z*} > 0`, and `s_{Z*}` maximizes `∑_{j ∈ Z*} log sⱼ` over the slacks
`s'` of the face with `s'_{Z*} > 0`. -/
def IsDualFaceAnalyticCenter (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (s : Fin n → ℝ) : Prop :=
  s ∈ DualOptimalFace A b c ∧ (∀ j ∈ Zstar A b c, 0 < s j) ∧
    ∀ s' ∈ DualOptimalFace A b c, (∀ j ∈ Zstar A b c, 0 < s' j) →
      ∑ j ∈ Zstar A b c, Real.log (s' j) ≤ ∑ j ∈ Zstar A b c, Real.log (s j)

/-- The centrality parameter `μ = xᵀs / n` (p. 73). -/
noncomputable def mu (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / n

/-- The one-sided "norm" of p. 73: `‖v‖_{−∞} = |min(0, min_j vⱼ)|`. For `n ≥ 1` the infimum over
the finite index set is the minimum; at `n = 0` it is `sInf ∅ = 0`, so the value is `0`. -/
noncomputable def negInfNorm (v : Fin n → ℝ) : ℝ :=
  |min 0 (⨅ j, v j)|

/-- The neighbourhood of the central path (p. 73), for a size function `nrm` on `ℝⁿ` (the book's
"‖.‖ can be any norm, or even a one-sided norm"):
`N(η) = {(x, y, s) ∈ F̊ : ‖Xs − μe‖ ≤ ημ, μ = xᵀs/n}`. -/
def InNeighborhood (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (nrm : (Fin n → ℝ) → ℝ) (η : ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  PrimalInterior A b x ∧ DualInterior A c y s ∧
    nrm (fun j => x j * s j - mu x s) ≤ η * mu x s

end YeIPA.Geometry


