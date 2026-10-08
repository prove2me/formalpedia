-- Prove2me | Definitions.Def_ConicQuadIPM_Homogeneous_Setting
-- name    : ConicQuadIPM_Homogeneous_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:11:49.277053+00:00
-- url     : https://prove2.me/theorems/bb0dbaec-fadb-4fe2-bdf5-daea47f29539
-- title:
--   §2.1–§2.2, pp. 4–6 — the conic pair (P)/(D), the dual cone (3), feasibility, optimality, infeasibility, and the homogeneous model (7)
-- statement:
--   This module fixes the objects of §2 of Andersen, Roos and Terlaky.
--
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let $K \subseteq \mathbb R^n$. The standing assumption of §2.1 is that $K$ is a **pointed closed convex cone**: $K$ is closed and convex, $tx \in K$ whenever $x \in K$ and $t \ge 0$, and $K$ is pointed, $K \cap (-K) = \{0\}$: it contains $0$, and $x \in K$, $-x \in K$ imply $x = 0$.
--
--   1. The **dual cone** (3) is
--   $$K_* := \{\, s \in \mathbb R^n : s^Tx \ge 0 \ \text{ for all } x \in K \,\}.$$
--   2. The **primal problem** (2) is $(P)$: minimize $c^Tx$ subject to $Ax = b$, $x \in K$. A point $x$ is *primal feasible* if $Ax = b$ and $x \in K$; it is *primal optimal* if it is primal feasible and $c^Tx \le c^Tx'$ for every primal feasible $x'$. $(P)$ is *infeasible* if it has no feasible point, and *strictly feasible* if some $x$ with $Ax = b$ lies in the interior $\operatorname{int}(K)$.
--   3. The **dual problem** (4) is $(D)$: maximize $b^Ty$ subject to $A^Ty + s = c$, $s \in K_*$. A pair $(y, s)$ is *dual feasible* if it satisfies these constraints and *dual optimal* if moreover $b^Ty' \le b^Ty$ for every dual feasible $(y', s')$. $(D)$ is *infeasible* if it has no feasible pair, and *strictly feasible* if some $(y,s)$ with $A^Ty + s = c$ has $s \in \operatorname{int}(K_*)$.
--   4. The **homogeneous model** (7) asks for $(x, \tau, y, s, \kappa) \in \mathbb R^n \times \mathbb R \times \mathbb R^m \times \mathbb R^n \times \mathbb R$ with
--   $$Ax - b\tau = 0,\qquad A^Ty + s - c\tau = 0,\qquad -c^Tx + b^Ty - \kappa = 0,\qquad (x;\tau) \in \bar K,\ (s;\kappa) \in \bar K_*,$$
--   where $\bar K := K \times \mathbb R_+$ and $\bar K_* := K_* \times \mathbb R_+$.
--
--   These are the objects in which weak and strong duality (Theorem 2.1), the infeasibility certificates (5)–(6) and Lemma 2.1 on the homogeneous model are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $u^Tv$ is `u ⬝ᵥ v`, $Ax$ is `A *ᵥ x`, $A^Ty$ is `Aᵀ *ᵥ y`. Optimality is an order predicate over all feasible points, not a value defined through $\inf$/$\sup$. $\bar K$ and $\bar K_*$ are unfolded into $x \in K,\ \tau \ge 0$ and $s \in K_*,\ \kappa \ge 0$. The interior in strict feasibility is the topological interior of $K$ (resp. $K_*$) in $\mathbb R^n$, as on p. 4. A nonempty interior of $K$ is not assumed.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, pp. 3–6, (2), (3), (4), the definitions of feasibility and strict feasibility on p. 4, and (7) with K̄, K̄_* on pp. 5–6

import Mathlib

namespace ConicQuadIPM.Homogeneous

open Matrix

/-- The standing assumption of §2.1 (Andersen, Roos & Terlaky, preprint of 18 Dec 2000, p. 4):
`K ⊆ ℝⁿ` is a **pointed closed convex cone**. Closed, convex, closed under multiplication by
nonnegative scalars, and pointed: `K ∩ (−K) = {0}`, i.e. `0 ∈ K` and `x ∈ K`, `-x ∈ K` force
`x = 0`. -/
def IsPointedClosedConvexCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  IsClosed K ∧ Convex ℝ K ∧ (∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K) ∧
    ((0 : Fin n → ℝ) ∈ K ∧ ∀ x ∈ K, -x ∈ K → x = 0)

/-- The dual cone (3), p. 4: `K_* := {s : sᵀx ≥ 0 ∀ x ∈ K}`. -/
def dualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {s | ∀ x ∈ K, 0 ≤ s ⬝ᵥ x}

/-- `x` is feasible for (P) (2): `Ax = b`, `x ∈ K`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ x ∈ K

/-- `(y, s)` is feasible for (D) (4): `Aᵀy + s = c`, `s ∈ K_*`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ y + s = c ∧ s ∈ dualCone K

/-- `x` is an optimal solution of (P): feasible, and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def PrimalOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  PrimalFeasible A b K x ∧ ∀ x', PrimalFeasible A b K x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- `(y, s)` is an optimal solution of (D): feasible, and `bᵀy' ≤ bᵀy` for every feasible
`(y', s')`. -/
def DualOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  DualFeasible A c K y s ∧ ∀ y' s', DualFeasible A c K y' s' → b ⬝ᵥ y' ≤ b ⬝ᵥ y

/-- (P) is infeasible: it has no feasible solution. -/
def PrimalInfeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (K : Set (Fin n → ℝ)) : Prop :=
  ¬ ∃ x, PrimalFeasible A b K x

/-- (D) is infeasible: it has no feasible solution. -/
def DualInfeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) : Prop :=
  ¬ ∃ y s, DualFeasible A c K y s

/-- (P) is strictly feasible (p. 4): some feasible `x` lies in `int(K)`. -/
def PrimalStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (K : Set (Fin n → ℝ)) : Prop :=
  ∃ x, A *ᵥ x = b ∧ x ∈ interior K

/-- (D) is strictly feasible (p. 4): some dual solution `(y, s)` has `s ∈ int(K_*)`. -/
def DualStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) : Prop :=
  ∃ y s, Aᵀ *ᵥ y + s = c ∧ s ∈ interior (dualCone K)

/-- The Goldman–Tucker homogeneous model (7), pp. 5–6, with `K̄ = K × ℝ₊`, `K̄_* = K_* × ℝ₊`:
`Ax − bτ = 0`, `Aᵀy + s − cτ = 0`, `−cᵀx + bᵀy − κ = 0`, `(x; τ) ∈ K̄`, `(s; κ) ∈ K̄_*`. -/
def HomFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ) :
    Prop :=
  A *ᵥ x - τ • b = 0 ∧ Aᵀ *ᵥ y + s - τ • c = 0 ∧ -(c ⬝ᵥ x) + b ⬝ᵥ y - κ = 0 ∧
    (x ∈ K ∧ 0 ≤ τ) ∧ (s ∈ dualCone K ∧ 0 ≤ κ)

end ConicQuadIPM.Homogeneous


