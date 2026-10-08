-- Prove2me | Definitions.Def_AffinePolicies_Simplex_Setting
-- name    : AffinePolicies_Simplex_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:14:01.26509+00:00
-- url     : https://prove2.me/theorems/9ffad2dc-8852-4507-927b-95b4fc48c9c4
-- title:
--   (1), PDF p. 2, and §2, PDF pp. 5–7 — Π_Adapt(𝒰), affine policies, z_Adapt, z_Aff, the simplex 𝒰 and the matrices Q, Y
-- statement:
--   **The two-stage adaptive problem.** Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$ and let $\mathcal U\subseteq\mathbb R^m$ be a set of possible right-hand sides. A **two-stage solution** consists of a first-stage vector $x\in\mathbb R^{n_1}$ and a second-stage rule $y:\mathbb R^m\to\mathbb R^{n_2}$, chosen after $b$ is revealed. It is **feasible** for $\Pi_{Adapt}(\mathcal U)$ when
--   $$x\ge 0,\qquad y(b)\ge 0,\qquad Ax+By(b)\ge b\quad\text{for every } b\in\mathcal U,$$
--   with all inequalities componentwise. A number $t$ **bounds the worst-case cost** of $(x,y)$ when $c^Tx+d^Ty(b)\le t$ for every $b\in\mathcal U$. The optimal value is
--   $$z_{Adapt}(\mathcal U)=\inf\{t : \text{some feasible }(x,y)\text{ has worst-case cost at most }t\},$$
--   which is $\min_x\, c^Tx+\max_{b\in\mathcal U} d^Ty(b)$ of model (1). An **affine policy** is a rule $y(b)=Pb+q$ with $P\in\mathbb R^{n_2\times m}$, $q\in\mathbb R^{n_2}$; $z_{Aff}(\mathcal U)$ is the same infimum restricted to affine policies (which must still satisfy $Pb+q\ge 0$ on $\mathcal U$). A feasible $(x,y)$ is **optimal** for $\Pi_{Adapt}(\mathcal U)$ when every worst-case bound achieved by any feasible two-stage solution is also achieved by $(x,y)$, i.e. when $(x,y)$ attains $z_{Adapt}(\mathcal U)$; optimality among affine solutions is defined in the same way with both sides restricted to affine policies.
--
--   **The simplex.** Given points $b^1,\dots,b^{m+1}\in\mathbb R^m$, the uncertainty set is $\mathcal U=\operatorname{conv}(b^1,\dots,b^{m+1})$. The matrix
--   $$Q=\big[(b^1-b^{m+1})\ \cdots\ (b^m-b^{m+1})\big]\in\mathbb R^{m\times m}$$
--   has the edge vectors from $b^{m+1}$ as columns. For a second-stage rule $g$, display (2) defines
--   $$Y=\big[(g(b^1)-g(b^{m+1}))\ \cdots\ (g(b^m)-g(b^{m+1}))\big]\in\mathbb R^{n_2\times m},$$
--   and the **affine interpolant** of $g$ is $\tilde y(b)=YQ^{-1}(b-b^{m+1})+g(b^{m+1})$.
--
--   These are the objects of Section 2 of the paper, where $g=y^*$ is an optimal second-stage solution and $\tilde y$ is shown to be an optimal affine policy.
--
--   **Formalization Note** Vectors are functions on `Fin m`; the paper's $b^j$ ($j=1,\dots,m+1$) is `v (j-1)`, and $b^{m+1}$ is `v (Fin.last m)`, so column $j-1$ of $Q$ is $b^j-b^{m+1}$. The values $z_{Adapt}$ and $z_{Aff}$ are infima of the sets of achievable worst-case bounds; Lean's real infimum returns $0$ on an empty set, so they are meaningful only when the problem is feasible (the theorems state optimality through attainment and do not depend on these values). $Q^{-1}$ is Mathlib's matrix inverse, which is the true inverse when $\det Q\ne 0$. Optimality is stated as attainment of every achievable bound, which avoids taking a real supremum of a possibly unbounded worst-case cost.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (1), PDF p. 2; Theorem 1 and its proof (Q, (2), ỹ), PDF pp. 5–7

import Mathlib

namespace AffinePolicies.Simplex

open Matrix

variable {m n₁ n₂ : ℕ}

/-- `(x, y)` is feasible for `Π_Adapt(U)` (model (1)): `x ≥ 0` and, for every `b ∈ U`,
`y(b) ≥ 0` and `A x + B y(b) ≥ b` (componentwise). -/
def Feasible (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (U : Set (Fin m → ℝ)) (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) : Prop :=
  0 ≤ x ∧ ∀ b ∈ U, 0 ≤ y b ∧ b ≤ A *ᵥ x + B *ᵥ y b

/-- `t` bounds the worst-case cost of `(x, y)` over `U`: `cᵀx + dᵀy(b) ≤ t` for every `b ∈ U`. -/
def CostLE (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ) : Prop :=
  ∀ b ∈ U, c ⬝ᵥ x + d ⬝ᵥ y b ≤ t

/-- `z_Adapt(U)`: the infimum of the worst-case costs achieved by feasible two-stage solutions. -/
noncomputable def zAdapt (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
    Feasible A B U x y ∧ CostLE c d U x y t}

/-- The affine second-stage policy `b ↦ P b + q`. -/
def affinePolicy (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ) :
    (Fin m → ℝ) → Fin n₂ → ℝ :=
  fun b => P *ᵥ b + q

/-- `z_Aff(U)`: the infimum of the worst-case costs achieved by feasible solutions whose
second stage is an affine policy. -/
noncomputable def zAff (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
    Feasible A B U x (affinePolicy P q) ∧ CostLE c d U x (affinePolicy P q) t}

/-- `(x, y)` is an optimal solution of `Π_Adapt(U)`: it is feasible, and every worst-case cost
bound achieved by any feasible two-stage solution is also achieved by `(x, y)`. -/
def IsOptimalAdapt (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) : Prop :=
  Feasible A B U x y ∧
    ∀ (x' : Fin n₁ → ℝ) (y' : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ),
      Feasible A B U x' y' → CostLE c d U x' y' t → CostLE c d U x y t

/-- `(x, P, q)` is an optimal affine solution: it is feasible, and every worst-case cost bound
achieved by any feasible solution with an affine second stage is also achieved by it. -/
def IsOptimalAff (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ) : Prop :=
  Feasible A B U x (affinePolicy P q) ∧
    ∀ (x' : Fin n₁ → ℝ) (P' : Matrix (Fin n₂) (Fin m) ℝ) (q' : Fin n₂ → ℝ) (t : ℝ),
      Feasible A B U x' (affinePolicy P' q') → CostLE c d U x' (affinePolicy P' q') t →
        CostLE c d U x (affinePolicy P q) t

/-- The simplex `conv(b¹, …, b^{m+1})` spanned by the vertices `v`; the paper's `bʲ` is
`v (j - 1)` and `b^{m+1}` is `v (Fin.last m)`. -/
noncomputable def simplexSet (v : Fin (m + 1) → Fin m → ℝ) : Set (Fin m → ℝ) :=
  convexHull ℝ (Set.range v)

/-- `Q = [(b¹ − b^{m+1}) … (b^m − b^{m+1})]`: column `j` (0-based) is `v j − v (Fin.last m)`. -/
def Qmat (v : Fin (m + 1) → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => v (Fin.castSucc j) i - v (Fin.last m) i

/-- `Y = [(g(b¹) − g(b^{m+1})) … (g(b^m) − g(b^{m+1}))]` for a second-stage map `g`
(display (2) with `g = y*`). -/
def Ymat (v : Fin (m + 1) → Fin m → ℝ) (g : (Fin m → ℝ) → Fin n₂ → ℝ) :
    Matrix (Fin n₂) (Fin m) ℝ :=
  Matrix.of fun i j => g (v (Fin.castSucc j)) i - g (v (Fin.last m)) i

/-- The affine interpolant `ỹ(b) = Y Q⁻¹ (b − b^{m+1}) + g(b^{m+1})` of the values of `g` at the
vertices of the simplex. -/
noncomputable def interpolant (v : Fin (m + 1) → Fin m → ℝ) (g : (Fin m → ℝ) → Fin n₂ → ℝ) :
    (Fin m → ℝ) → Fin n₂ → ℝ :=
  fun b => (Ymat v g * (Qmat v)⁻¹) *ᵥ (b - v (Fin.last m)) + g (v (Fin.last m))

end AffinePolicies.Simplex


