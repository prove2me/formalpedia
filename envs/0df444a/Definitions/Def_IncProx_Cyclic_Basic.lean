-- Prove2me | Definitions.Def_IncProx_Cyclic_Basic
-- name    : IncProx_Cyclic_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:23.718576+00:00
-- url     : https://prove2.me/theorems/5cfaa90d-7605-4c89-ae6d-c159be0dda1f
-- title:
--   Problem (5)–(6), $F^*$, $X^*$, the iterations (19)–(21) with a cyclic order, and Assumptions 1–2
-- statement:
--   This file fixes the objects of Bertsekas' analysis of incremental subgradient-proximal methods with a cyclic order.
--
--   **Space.** $\mathbb R^n$ carries the standard Euclidean norm $\|\cdot\|$ and inner product $x'y$. A vector $g$ is a **subgradient** of a real-valued function $f$ at $x$ if $f(x)+g'(y-x)\le f(y)$ for all $y$; we write $g=\tilde\nabla f(x)$. A point $p$ is the **projection** $P_X(u)$ of $u$ on a set $X$ if $p\in X$ and $\|u-p\|\le\|u-y\|$ for every $y\in X$.
--
--   **Problem (5)–(6).** The data are a set $X\subseteq\mathbb R^n$ and real-valued functions $f_i,h_i:\mathbb R^n\to\mathbb R$, $i=1,\dots,m$. The **standing assumptions** (p. 4) are that $X$ is nonempty, closed and convex and that every $f_i$ and $h_i$ is convex. The problem is
--   $$\text{minimize } F(x)=\sum_{i=1}^m F_i(x),\quad F_i=f_i+h_i,\quad\text{subject to } x\in X.$$
--   The **optimal value** is $F^*=\inf_{x\in X}F(x)\in[-\infty,\infty)$ and the **optimal set** is $X^*=\{x^*\in X: F(x^*)=F^*\}$, which may be empty.
--
--   **One step.** With component $i$ and stepsize $\alpha>0$, one step of each of the three iterations of p. 7 goes from $x$ through $z$ to $x'$:
--
--   1. (19): $z=P_X(x-\alpha\tilde\nabla f_i(z))$, $x'=P_X(z-\alpha\tilde\nabla h_i(z))$;
--   2. (20): $z=x-\alpha\tilde\nabla f_i(z)$, $x'=P_X(z-\alpha\tilde\nabla h_i(z))$;
--   3. (21): $z=x-\alpha\tilde\nabla h_i(x)$, $x'=P_X(z-\alpha\tilde\nabla f_i(x'))$.
--
--   The $f_i$-subgradient is taken at the point the step produces ($z$ or $x'$), which makes the $f_i$-part a proximal step; the $h_i$-subgradient may be any subgradient at the point named.
--
--   **Cyclic order and runs.** In the cyclic order the component used at iteration $k$ is $i_k=(k \bmod m)+1$. A **run** of iteration (19), (20) or (21) is a sequence $x_k$, $z_k$ with subgradients $\tilde\nabla f_{i_k}$, $\tilde\nabla h_{i_k}$ such that every iteration $k$ is one step from $x_k$ to $x_{k+1}$ with component $i_k$ and stepsize $\alpha_k$. The stepsizes are positive and constant within each cycle: $\alpha_k=\alpha_{m\lfloor k/m\rfloor}$.
--
--   **Assumption 1** (for (19), (20); p. 8). There is $c$ such that $\max\{\|\tilde\nabla f_{i_k}(z_k)\|,\|\tilde\nabla h_{i_k}(z_k)\|\}\le c$ for all $k$ (22), and for every cycle start $k>0$ and $j=1,\dots,m$
--   $$\max\{f_j(x_k)-f_j(z_{k+j-1}),\ h_j(x_k)-h_j(z_{k+j-1})\}\le c\,\|x_k-z_{k+j-1}\|.\qquad(23)$$
--
--   **Assumption 2** (for (21); p. 9). There is $c$ with $\max\{\|\tilde\nabla f_{i_k}(x_{k+1})\|,\|\tilde\nabla h_{i_k}(x_k)\|\}\le c$ for all $k$ (24), and for every cycle start $k>0$ and $j=1,\dots,m$, (25): $\max\{f_j(x_k)-f_j(x_{k+j-1}),\ h_j(x_k)-h_j(x_{k+j-1})\}\le c\|x_k-x_{k+j-1}\|$ and (26): $f_j(x_{k+j-1})-f_j(x_{k+j})\le c\|x_{k+j-1}-x_{k+j}\|$.
--
--   **The constant of Proposition 3** is $\beta=\frac1m+4$ for (19), (20) and $\beta=\frac5m+4$ for (21).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. Components are indexed by `Fin m` (0-based), so $i_k$ is `k % m` and the paper's $j=1,\dots,m$ with $z_{k+j-1}$, $x_{k+j-1}$, $x_{k+j}$ becomes $j=0,\dots,m-1$ with `z (k + j)`, `x (k + j)`, `x (k + j + 1)`. "$k$ marks the beginning of a cycle" is `k % m = 0`. $P_X$ is the predicate `IsProj` (a nearest point), not a choice function. $F^*$ is an `EReal` infimum so that $F^*=-\infty$ is representable, and $X^*$ is defined through it. The subgradient used by each step is part of the run (`gF k`, `gH k`), so Assumptions 1–2 bound exactly the subgradients the iteration uses. The paper's standing assumptions and the positivity of the stepsizes are explicit (`Problem.Standing`, `CyclicStepsize`); the cycle-start conditions (23), (25), (26) are stated, as on pp. 8–9, for cycle starts $k>0$ only.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), pp. 1–9: footnotes 1–2, problem (5)–(6) p. 4, iterations (19)–(21) and the cyclic order p. 7, F* and X* p. 8, Assumption 1 p. 8, Assumption 2 p. 9, β of Proposition 3 p. 9

import Mathlib

namespace IncProx.Cyclic

open Filter Topology

/-- ℝⁿ with the standard Euclidean norm ‖·‖ and inner product x′y (footnote 1). -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n m : ℕ}

/-- `g` is a subgradient of the real-valued function `f` at `x` (footnote 2: ∇̃f(x) ∈ ∂f(x)). -/
def IsSubgrad (f : Vec n → ℝ) (x g : Vec n) : Prop :=
  ∀ y, f x + inner ℝ g (y - x) ≤ f y

/-- `p = P_X(u)`: `p` is the Euclidean projection of `u` on `X` (a nearest point of `X`). -/
def IsProj (X : Set (Vec n)) (u p : Vec n) : Prop :=
  p ∈ X ∧ ∀ y ∈ X, ‖u - p‖ ≤ ‖u - y‖

/-- The data of problem (5)–(6): the set `X` and the components `f i`, `h i`, `i : Fin m`. -/
structure Problem (n m : ℕ) where
  X : Set (Vec n)
  f : Fin m → Vec n → ℝ
  h : Fin m → Vec n → ℝ

namespace Problem

/-- Standing assumptions (p. 4): `X` nonempty closed convex; `f i`, `h i` real-valued convex. -/
structure Standing (P : Problem n m) : Prop where
  X_nonempty : P.X.Nonempty
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  f_convex : ∀ i, ConvexOn ℝ Set.univ (P.f i)
  h_convex : ∀ i, ConvexOn ℝ Set.univ (P.h i)

/-- `F_i = f_i + h_i` (6). -/
def Fi (P : Problem n m) (i : Fin m) (x : Vec n) : ℝ := P.f i x + P.h i x

/-- `F = Σ_i F_i` (5). -/
noncomputable def F (P : Problem n m) (x : Vec n) : ℝ := ∑ i, P.Fi i x

/-- `F* = inf_{x ∈ X} F(x)` (p. 8), in `EReal`: it may be `−∞`. -/
noncomputable def Fstar (P : Problem n m) : EReal := ⨅ x ∈ P.X, ((P.F x : ℝ) : EReal)

/-- `X* = {x* ∈ X | F(x*) = F*}` (p. 8); possibly empty. -/
def Xstar (P : Problem n m) : Set (Vec n) := {x | x ∈ P.X ∧ ((P.F x : ℝ) : EReal) = P.Fstar}

end Problem

/-- The three iterations (19), (20), (21) of p. 7. -/
inductive Alg
  | a19 | a20 | a21

/-- One step of iteration (19), (20) or (21) with component `i` and stepsize `a`: from `x` through
`z` to `x'`, where `gF` is the subgradient of `f i` and `gH` the subgradient of `h i` the step uses.
(19): z = P_X(x − a gF), gF ∈ ∂f_i(z);  x' = P_X(z − a gH), gH ∈ ∂h_i(z).
(20): z = x − a gF,      gF ∈ ∂f_i(z);  x' = P_X(z − a gH), gH ∈ ∂h_i(z).
(21): z = x − a gH,      gH ∈ ∂h_i(x);  x' = P_X(z − a gF), gF ∈ ∂f_i(x'). -/
def Step (P : Problem n m) : Alg → Fin m → ℝ → Vec n → Vec n → Vec n → Vec n → Vec n → Prop
  | .a19, i, a, x, z, gF, gH, x' => IsSubgrad (P.f i) z gF ∧ IsProj P.X (x - a • gF) z ∧
      IsSubgrad (P.h i) z gH ∧ IsProj P.X (z - a • gH) x'
  | .a20, i, a, x, z, gF, gH, x' => IsSubgrad (P.f i) z gF ∧ z = x - a • gF ∧
      IsSubgrad (P.h i) z gH ∧ IsProj P.X (z - a • gH) x'
  | .a21, i, a, x, z, gF, gH, x' => IsSubgrad (P.h i) x gH ∧ z = x - a • gH ∧
      IsSubgrad (P.f i) x' gF ∧ IsProj P.X (z - a • gF) x'

/-- The cyclic order (p. 7): i_k = (k modulo m) + 1, here 0-based: i_k = k mod m. -/
def cyc [NeZero m] (k : ℕ) : Fin m := ⟨k % m, Nat.mod_lt k (NeZero.pos m)⟩

/-- A sequence generated by iteration `A` with component sequence `i` and stepsizes `α`:
x_k, z_k, and the subgradients gF k (of f_{i_k}) and gH k (of h_{i_k}) the k-th step uses. -/
def IsRun (P : Problem n m) (A : Alg) (i : ℕ → Fin m) (α : ℕ → ℝ)
    (x z gF gH : ℕ → Vec n) : Prop :=
  ∀ k, Step P A (i k) (α k) (x k) (z k) (gF k) (gH k) (x (k + 1))

/-- Positive stepsizes (p. 2–3), constant within a cycle (p. 7, order (1)):
α_k = α_{m⌊k/m⌋}, the stepsize at the start of the cycle containing k. -/
def CyclicStepsize (m : ℕ) (α : ℕ → ℝ) : Prop :=
  (∀ k, 0 < α k) ∧ ∀ k, α k = α (m * (k / m))

/-- Assumption 1 (p. 8), for iterations (19) and (20): (22) for all k and, at every cycle start
k > 0 (k mod m = 0), (23) for every j. `gF k` is ∇̃f_{i_k}(z_k), `gH k` is ∇̃h_{i_k}(z_k); the
paper's j = 1, …, m and z_{k+j−1} become `j : Fin m` (0-based) and `z (k + j)`. -/
def Assumption1 (P : Problem n m) (x z gF gH : ℕ → Vec n) (c : ℝ) : Prop :=
  (∀ k, ‖gF k‖ ≤ c ∧ ‖gH k‖ ≤ c) ∧
  ∀ k, 0 < k → k % m = 0 → ∀ j : Fin m,
    P.f j (x k) - P.f j (z (k + (j : ℕ))) ≤ c * ‖x k - z (k + (j : ℕ))‖ ∧
    P.h j (x k) - P.h j (z (k + (j : ℕ))) ≤ c * ‖x k - z (k + (j : ℕ))‖

/-- Assumption 2 (p. 9), for iteration (21): (24) for all k and, at every cycle start k > 0,
(25) and (26) for every j. `gF k` is ∇̃f_{i_k}(x_{k+1}), `gH k` is ∇̃h_{i_k}(x_k); the paper's
x_{k+j−1}, x_{k+j} (j = 1, …, m) become `x (k + j)`, `x (k + j + 1)` with `j : Fin m` 0-based. -/
def Assumption2 (P : Problem n m) (x gF gH : ℕ → Vec n) (c : ℝ) : Prop :=
  (∀ k, ‖gF k‖ ≤ c ∧ ‖gH k‖ ≤ c) ∧
  ∀ k, 0 < k → k % m = 0 → ∀ j : Fin m,
    P.f j (x k) - P.f j (x (k + (j : ℕ))) ≤ c * ‖x k - x (k + (j : ℕ))‖ ∧
    P.h j (x k) - P.h j (x (k + (j : ℕ))) ≤ c * ‖x k - x (k + (j : ℕ))‖ ∧
    P.f j (x (k + (j : ℕ))) - P.f j (x (k + (j : ℕ) + 1)) ≤
      c * ‖x (k + (j : ℕ)) - x (k + (j : ℕ) + 1)‖

/-- The assumption that goes with each iteration: Assumption 1 for (19), (20); Assumption 2 for (21). -/
def AssumptionFor (P : Problem n m) : Alg → (x z gF gH : ℕ → Vec n) → ℝ → Prop
  | .a21, x, _, gF, gH, c => Assumption2 P x gF gH c
  | .a19, x, z, gF, gH, c => Assumption1 P x z gF gH c
  | .a20, x, z, gF, gH, c => Assumption1 P x z gF gH c

/-- β of Proposition 3: 1/m + 4 for (19) and (20), 5/m + 4 for (21). -/
noncomputable def beta (m : ℕ) : Alg → ℝ
  | .a21 => 5 / (m : ℝ) + 4
  | .a19 => 1 / (m : ℝ) + 4
  | .a20 => 1 / (m : ℝ) + 4

end IncProx.Cyclic


