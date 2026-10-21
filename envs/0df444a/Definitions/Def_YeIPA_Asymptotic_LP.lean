-- Prove2me | Definitions.Def_YeIPA_Asymptotic_LP
-- name    : YeIPA_Asymptotic_LP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:29.101437+00:00
-- url     : https://prove2.me/theorems/ac0edef8-3371-4f80-86ee-7ba76f1a9422
-- title:
--   Standard-form LP, the partition $(P^*,Z^*)$, the neighbourhood $\mathcal N_2(\eta)$, the scaling $D=X^{1/2}S^{-1/2}$, the predictor system (7.4) and Algorithm 4.5
-- statement:
--   Fix a real $m\times n$ matrix $A$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$, and consider the standard-form pair
--   $$(\mathrm{LP})\ \min\{c^Tx: Ax=b,\ x\ge0\},\qquad (\mathrm{LD})\ \max\{b^Ty: A^Ty+s=c,\ s\ge0\}.$$
--   Vector inequalities are componentwise, $X=\operatorname{diag}(x)$, $S=\operatorname{diag}(s)$ and $e$ is the all-ones vector. This module defines the objects Chapter 7 of Ye's *Interior Point Algorithms* works with.
--
--   1. **Feasibility, interior points, optimality.** $x$ is primal feasible if $Ax=b$, $x\ge0$; $(y,s)$ is dual feasible if $A^Ty+s=c$, $s\ge0$; $(x,y,s)$ is an **interior point** ($(x,y,s)\in\mathring{\mathcal F}$) if $Ax=b$, $x>0$, $A^Ty+s=c$, $s>0$. Optimality is minimality of $c^Tx$ over primal feasible points, maximality of $b^Ty$ over dual feasible points.
--   2. **The strict complementarity partition** (Theorem 1.14, p. 20; Chapter 7 writes $(P,Z)=(P^*,Z^*)$, p. 214): $P^*=\{j: x^*_j>0$ for some optimal $x^*\}$ and $Z^*=\{j: s^*_j>0$ for some optimal $(y^*,s^*)\}$.
--   3. **The neighbourhood** (p. 128): with $\mu=x^Ts/n$,
--   $$\mathcal N_2(\eta)=\{(x,y,s)\in\mathring{\mathcal F}:\ \|Xs-\mu e\|\le\eta\mu\},$$
--   $\|\cdot\|$ the Euclidean norm.
--   4. **The scaling** $D=X^{1/2}S^{-1/2}$ (p. 214), the diagonal matrix with entries $D_j=\sqrt{x_j/s_j}$, and the Euclidean norm $\|v_S\|=(\sum_{j\in S}v_j^2)^{1/2}$ of the subvector indexed by $S$.
--   5. **The direction** $d=d(x,s,\gamma)=(d_x,d_y,d_s)$ of system (4.17) (p. 126):
--   $$Sd_x+Xd_s=\gamma\mu e-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0.$$
--   For $\gamma=0$ this is the **predictor system** (7.4) (p. 213): $Xd_s+Sd_x=-Xs$, $Ad_x=0$, $-A^Td_y-d_s=0$.
--   6. **The largest step** (p. 131, notation (4.19)): $\bar\theta$ is the largest $\theta'\ge0$ such that $(x+\theta d_x,\ y+\theta d_y,\ s+\theta d_s)\in\mathcal N_2(\eta')$ for every $\theta\in[0,\theta']$.
--   7. **Algorithm 4.5** (predictor-corrector, p. 131) with $\eta=1/4$: start from $(x^0,y^0,s^0)\in\mathcal N_2(1/4)$; at iteration $k$, compute $d=d(x^k,s^k,0)$ and the largest step $\theta^k=\bar\theta$ keeping the iterate in $\mathcal N_2(2\eta)=\mathcal N_2(1/2)$; set $(x',y',s')=(x^k,y^k,s^k)+\bar\theta d$, compute $d'=d(x',s',1)$, and set $(x^{k+1},y^{k+1},s^{k+1})=(x',y',s')+d'$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, so indices $1,\dots,n$ become $0,\dots,n-1$; matrices are `Matrix (Fin m) (Fin n) ℝ`. $P^*$ and $Z^*$ are unions of supports of optimal solutions, which is the book's partition whenever optimal solutions exist (Theorem 1.14); every theorem of the mission has an interior point among its hypotheses, so they exist. $\mu=x^Ts/n$ uses Lean's division, so $\mu=0$ when $n=0$. $\|v_S\|$ is written as the Euclidean norm of the vector equal to $v$ on $S$ and $0$ off $S$. The book's algorithm stops once $(x^k)^Ts^k\le\epsilon$; the run here is continued for every $k$ (the asymptotic analysis of Chapter 7 is about this infinite sequence), and the dual iterates $y^k$ are carried along although the book lists only $(x^k,s^k)$. The largest step is `IsGreatest` of the set of admissible $\theta'$; when that set has no greatest element there is no run.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 18–20 ((LP), (LD), Theorem 1.14), p. 126 ((4.17)), pp. 128–131 (N₂(η), (4.19), Algorithm 4.5), pp. 213–214 ((7.4), D)

import Mathlib

open Matrix

namespace YeIPA.Asymptotic

/-!
# Standard-form LP, the strict complementarity partition, the neighbourhood `N₂(η)`, the
# predictor system (7.4) and the predictor-corrector Algorithm 4.5

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997: (LP) and (LD) pp. 18–19;
the strict complementarity partition `(P*, Z*)` (Theorem 1.14, p. 20; Chapter 7 writes
`(P, Z) = (P*, Z*)`, p. 214); the neighbourhood `N₂(η)` (p. 128); the direction
`d(x, s, γ)` of system (4.17) (p. 126), whose case `γ = 0` is the predictor system (7.4)
(p. 213); the scaling `D = X^{1/2} S^{-1/2}` (p. 214); Algorithm 4.5 (p. 131).

`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`. The book's indices
`1, …, n` are `0, …, n-1` here. Vector inequalities are componentwise.
-/

variable {m n : ℕ}

/-- `x` is feasible for (LP) `minimize cᵀx s.t. Ax = b, x ≥ 0` (p. 18). -/
def PrimalFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j

/-- `(y, s)` is feasible for (LD) `maximize bᵀy s.t. Aᵀy + s = c, s ≥ 0` (p. 19). -/
def DualFeasible (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 ≤ s j

/-- `(x, y, s)` is an interior feasible point, the book's `(x, y, s) ∈ F̊`:
`Ax = b`, `x > 0`, `Aᵀy + s = c`, `s > 0`. -/
def IsInterior (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ (∀ j, 0 < x j) ∧ Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 < s j

/-- `x` is an optimal solution of (LP): feasible, and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def IsPrimalOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- `(y, s)` is an optimal solution of (LD): feasible, and `bᵀy' ≤ bᵀy` for every feasible
`(y', s')`. -/
def IsDualOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  DualFeasible A c y s ∧ ∀ y' s', DualFeasible A c y' s' → b ⬝ᵥ y' ≤ b ⬝ᵥ y

/-- `P = P*`, the primal part of the strict complementarity partition (Theorem 1.14, p. 20):
the indices `j` with `x*ⱼ > 0` for some optimal solution `x*` of (LP). -/
def Pstar (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Set (Fin n) :=
  {j | ∃ x, IsPrimalOptimal A b c x ∧ 0 < x j}

/-- `Z = Z*`, the dual part of the strict complementarity partition (Theorem 1.14, p. 20):
the indices `j` with `s*ⱼ > 0` for some optimal solution `(y*, s*)` of (LD). -/
def Zstar (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Set (Fin n) :=
  {j | ∃ y s, IsDualOptimal A b c y s ∧ 0 < s j}

/-- `μ = xᵀs / n` (p. 128, p. 213). -/
noncomputable def mu (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / n

/-- The neighbourhood `N₂(η)` of the central path (p. 128):
`(x, y, s) ∈ F̊` and `‖Xs − μe‖ ≤ ημ` with `μ = xᵀs/n`, `‖·‖` the Euclidean norm. -/
def InN2 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (η : ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  IsInterior A b c x y s ∧
    Real.sqrt (∑ j, (x j * s j - mu x s) ^ 2) ≤ η * mu x s

/-- The diagonal of the scaling matrix `D = X^{1/2} S^{-1/2}` (p. 214): `Dⱼ = √(xⱼ / sⱼ)`. -/
noncomputable def scaling (x s : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.sqrt (x j / s j)

/-- The Euclidean norm `‖v_S‖` of the subvector of `v` indexed by `S ⊆ {1, …, n}`. -/
noncomputable def normOn (S : Set (Fin n)) (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j, (S.indicator v j) ^ 2)

/-- `d = (d_x, d_y, d_s)` solves system (4.17) (p. 126) at `(x, s)` with parameter `γ`:
`S d_x + X d_s = γμe − Xs`, `A d_x = 0`, `−Aᵀ d_y − d_s = 0`, where `μ = xᵀs/n`.
The book writes `d = d(x, s, γ)`. -/
def IsDirection (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * mu x s - x j * s j) ∧ A *ᵥ dx = 0 ∧
    -(Aᵀ *ᵥ dy) - ds = 0

/-- `(d_x, d_y, d_s)` solves the predictor system (7.4) (p. 213) at `(x, s)`:
`X d_s + S d_x = −Xs`, `A d_x = 0`, `−Aᵀ d_y − d_s = 0`; this is (4.17) with `γ = 0`. -/
def IsPredictorDirection (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  IsDirection A x s 0 dx dy ds

/-- `θ̄` is the largest step so that `(x(θ), y(θ), s(θ)) = (x + θd_x, y + θd_y, s + θd_s)`
stays in `N₂(η')` for every `θ ∈ [0, θ̄]` (the step rule of Algorithm 4.5, p. 131, with
`η' = 2η`; notation (4.19), p. 129). -/
def IsLargestStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (η' : ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ) : Prop :=
  IsGreatest {θ' : ℝ | 0 ≤ θ' ∧ ∀ θ ∈ Set.Icc 0 θ',
      InN2 A b c η' (x + θ • dx) (y + θ • dy) (s + θ • ds)} θbar

/-- `(xᵏ, yᵏ, sᵏ)` with predictor step sizes `θᵏ` is a run of Algorithm 4.5 (p. 131) with
`η = 1/4`, continued for every `k` (the termination test `(xᵏ)ᵀsᵏ > ε` is not applied):
`(x⁰, y⁰, s⁰) ∈ N₂(1/4)`, and at every `k`
1. (predictor) `d = d(xᵏ, sᵏ, 0)` and `θᵏ = θ̄` is the largest step with
   `(x(θ), s(θ)) ∈ N₂(2η) = N₂(1/2)` for all `θ ∈ [0, θ̄]`;
2. (corrector) `(x', y', s') = (x(θ̄), y(θ̄), s(θ̄))`, `d' = d(x', s', 1)`, and
   `(xᵏ⁺¹, yᵏ⁺¹, sᵏ⁺¹) = (x' + d'_x, y' + d'_y, s' + d'_s)`. -/
def IsAlgorithm45Run (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (θ : ℕ → ℝ) : Prop :=
  InN2 A b c (1 / 4) (x 0) (y 0) (s 0) ∧
    ∀ k, ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
      (dx' : Fin n → ℝ) (dy' : Fin m → ℝ) (ds' : Fin n → ℝ),
      IsDirection A (x k) (s k) 0 dx dy ds ∧
      IsLargestStep A b c (2 * (1 / 4)) (x k) (y k) (s k) dx dy ds (θ k) ∧
      IsDirection A (x k + θ k • dx) (s k + θ k • ds) 1 dx' dy' ds' ∧
      x (k + 1) = x k + θ k • dx + dx' ∧
      y (k + 1) = y k + θ k • dy + dy' ∧
      s (k + 1) = s k + θ k • ds + ds'

end YeIPA.Asymptotic


