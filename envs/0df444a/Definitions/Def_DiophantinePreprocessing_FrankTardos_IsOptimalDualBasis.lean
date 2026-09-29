-- Prove2me | Definitions.Def_DiophantinePreprocessing_FrankTardos_IsOptimalDualBasis
-- name    : DiophantinePreprocessing_FrankTardos_IsOptimalDualBasis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:39:58.299708+00:00
-- url     : https://prove2.me/theorems/6881b9be-394c-4632-aca4-4ae624f736af
-- title:
--   Dual bases and optimal dual bases of $\max\{wx : Ax \le b\}$
-- statement:
--   Let $A$ be an $m \times n$ integer matrix, $b \in \mathbb{R}^m$ and $w \in \mathbb{R}^n$, and consider the dual program
--   $$\text{(1b)} \qquad \min\ yb \quad \text{subject to} \quad yA = w,\ y \ge 0 \qquad (y \in \mathbb{R}^m).$$
--
--   1. A **dual basis** is a set $B$ of row indices of $A$ such that the rows indexed by $B$ are linearly independent over $\mathbb{R}$ and no strictly larger set of row indices has linearly independent rows. Two equal rows with different indices are different rows.
--   2. $y$ is **dual feasible** if $y \ge 0$ and $yA = w$, and **dual optimal** if it is dual feasible and $yb \le y'b$ for every dual feasible $y'$.
--   3. A dual basis $B$ determines at most one vector $y$ with $yA = w$ and $y_i = 0$ for $i \notin B$ (the basic dual solution). $B$ is an **optimal dual basis** for $\max\{wx : Ax \le b\}$ if this $y$ exists and is an optimal solution of (1b).
--
--   Theorem 4.2 (ii) asserts that the rounded objective $\tilde w$ has the same optimal dual bases as $w$.
--
--   **Formalization Note** "Optimal dual basis" is encoded as: $B$ is a dual basis and some $y$ supported on $B$ is dual optimal. Since the rows of $B$ are independent, such a $y$ is unique, so the existential is the paper's basic dual solution. The support condition, implicit on p. 57, is taken from the proof of Lemma 4.1, where $y' = (y'_B, y'_N)$ with $y'_N = 0$.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 57, (1) and the definitions of dual basis, feasible dual basis, basic dual solution and optimal dual basis

import Mathlib

namespace DiophantinePreprocessing.FrankTardos

/-- A dual basis of `A`: a set `B` of row indices whose rows are linearly independent over `ℝ`
and which is maximal with this property (no strictly larger set of row indices has linearly
independent rows). Equal rows with different indices count as different rows. -/
def IsDualBasis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (B : Finset (Fin m)) : Prop :=
  LinearIndependent ℝ (fun i : B => fun j => (A i.1 j : ℝ)) ∧
  ∀ B' : Finset (Fin m), B ⊆ B' →
    LinearIndependent ℝ (fun i : B' => fun j => (A i.1 j : ℝ)) → B' = B

/-- `y` is feasible for the dual program (1b): `y ≥ 0` and `y A = w`. -/
def IsDualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (w : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, ∑ i, y i * (A i j : ℝ) = w j

/-- `y` is an optimal solution of the dual program (1b): `min y b` subject to `y A = w, y ≥ 0`. -/
def IsDualOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ) (w : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  IsDualFeasible A w y ∧
    ∀ y' : Fin m → ℝ, IsDualFeasible A w y' → ∑ i, y i * b i ≤ ∑ i, y' i * b i

/-- `B` is an optimal dual basis for `max (w x : A x ≤ b)`: `B` is a dual basis and the vector
`y` it determines (the solution of `y A = w` supported on `B`, unique when it exists) is an
optimal solution of the dual program (1b). -/
def IsOptimalDualBasis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ)
    (w : Fin n → ℝ) (B : Finset (Fin m)) : Prop :=
  IsDualBasis A B ∧ ∃ y : Fin m → ℝ, (∀ i, i ∉ B → y i = 0) ∧ IsDualOptimal A b w y

end DiophantinePreprocessing.FrankTardos


