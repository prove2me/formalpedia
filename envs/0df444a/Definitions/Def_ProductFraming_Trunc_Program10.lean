-- Prove2me | Definitions.Def_ProductFraming_Trunc_Program10
-- name    : ProductFraming_Trunc_Program10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:46.951819+00:00
-- url     : https://prove2.me/theorems/c7f7576b-aa68-4ceb-883a-a1aa26108390
-- title:
--   The bound-revealing program (10), its objective, optimal solutions and largest maximizers
-- statement:
--   Program (10) has as variables two functions on $[m]$: $U$ and a tail function $\Lambda$, with $\lambda(x)=\Lambda(x)-\Lambda(x+1)$ for $x\in[m]$ and $\Lambda(m+1)=0$. Its constraints are
--
--   $$
--   \begin{aligned}
--   &1=\Lambda(1)\ge\Lambda(2)\ge\cdots\ge\Lambda(m)\ge 0,\\
--   &\Lambda(x+1)\Lambda(x-1)\le\Lambda(x)^2,\quad x=2,\dots,m-1,\\
--   &U(x)\le U(x+1),\quad \frac{U(x)}{x}\ge\frac{U(x+1)}{x+1},\quad x=1,\dots,m-1,\\
--   &\mathbf E[U(X)]=\sum_{x\in[m]}\lambda(x)U(x)=1,\qquad U(x)\ge 0,\quad x\in[m],
--   \end{aligned}
--   $$
--
--   and its objective, to be minimized, is
--   $$J(U,\Lambda)=\max_{x\in[m]}U(x)\Lambda(x).$$
--   The failure rate of $\Lambda$ is $h(x)=\lambda(x)/\Lambda(x)$. A feasible pair is **optimal** if its objective value is at most that of every feasible pair. Finally, $y$ is the **largest maximizer** of a function $\varphi$ on $[m]$ (the paper's $\operatorname{maxarg\,max}_{x\in[m]}\varphi(x)$) if $\varphi(x)\le\varphi(y)$ for all $x\in[m]$ and $\varphi(x)<\varphi(y)$ for all $x\in[m]$ with $x>y$.
--
--   Program (10) reduces Theorem 4 to a statement about pairs $(U,\Lambda)$: its optimal value lower-bounds the ratio between the TRUNC revenue and the upper bound $\mathbf E[U(X)]$.
--
--   **Formalization Note** $U$ and $\Lambda$ are functions `ℕ → ℝ` (the tail is written `L`) whose values outside $[m]$ are irrelevant; $\lambda(m)=\Lambda(m)$ is built into `lamOfTail`. The objective `J10` takes the hypothesis $1\le m$ as an argument so that the maximum is over a nonempty set.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, (10), p. 15; A.4, p. 39

import Mathlib
open Finset

namespace ProductFraming.Trunc

/-! The bound-revealing program (10) (p. 15) and the objects of Appendix A.4 (p. 39).
The variables are two functions on `[m] = {1, …, m}`: `U` and the tail function `L` (the
paper's `Λ`). Values outside `[m]` are never used. -/

/-- `λ(x) = Λ(x) − Λ(x+1)` for `x ∈ [m]`, with the convention `Λ(m+1) = 0` (so `λ(m) = Λ(m)`). -/
def lamOfTail (m : ℕ) (L : ℕ → ℝ) (x : ℕ) : ℝ :=
  L x - (if x < m then L (x + 1) else 0)

/-- The failure rate `h(x) = λ(x)/Λ(x)` of the tail function `L` (A.4, p. 39). -/
noncomputable def hazard (m : ℕ) (L : ℕ → ℝ) (x : ℕ) : ℝ :=
  lamOfTail m L x / L x

/-- The constraints of program (10), p. 15. -/
structure Feasible10 (m : ℕ) (U L : ℕ → ℝ) : Prop where
  /-- `1 = Λ(1)` -/
  tail_one : L 1 = 1
  /-- `Λ(1) ≥ Λ(2) ≥ ⋯ ≥ Λ(m)` -/
  tail_antitone : ∀ x : ℕ, 1 ≤ x → x < m → L (x + 1) ≤ L x
  /-- `Λ(m) ≥ 0` -/
  tail_nonneg : 0 ≤ L m
  /-- `Λ(x+1)Λ(x−1) ≤ Λ(x)²` for `x = 2, 3, …, m−1` -/
  logconcave : ∀ x : ℕ, 2 ≤ x → x + 1 ≤ m → L (x + 1) * L (x - 1) ≤ L x ^ 2
  /-- `U(x) ≤ U(x+1)` for `x = 1, …, m−1` -/
  U_mono : ∀ x : ℕ, 1 ≤ x → x < m → U x ≤ U (x + 1)
  /-- `U(x)/x ≥ U(x+1)/(x+1)` for `x = 1, …, m−1` -/
  U_div_antitone : ∀ x : ℕ, 1 ≤ x → x < m → U (x + 1) / ((x : ℝ) + 1) ≤ U x / (x : ℝ)
  /-- `E[U(X)] = ∑_{x ∈ [m]} λ(x) U(x) = 1` -/
  expect_eq_one : ∑ x ∈ Icc 1 m, lamOfTail m L x * U x = 1
  /-- `U(x) ≥ 0` for `x ∈ [m]` -/
  U_nonneg : ∀ x ∈ Icc 1 m, 0 ≤ U x

/-- The objective of (10): `max_{x ∈ [m]} U(x)Λ(x)` (requires `1 ≤ m`). -/
noncomputable def J10 (m : ℕ) (hm : 1 ≤ m) (U L : ℕ → ℝ) : ℝ :=
  (Icc 1 m).sup' (nonempty_Icc.mpr hm) (fun x => U x * L x)

/-- `(U, L)` is an optimal solution of (10). -/
def IsOptimal10 (m : ℕ) (hm : 1 ≤ m) (U L : ℕ → ℝ) : Prop :=
  Feasible10 m U L ∧ ∀ U' L' : ℕ → ℝ, Feasible10 m U' L' → J10 m hm U L ≤ J10 m hm U' L'

/-- `y` is the largest maximizer of `φ` on `[m]` (the paper's `maxarg max_{x ∈ [m]} φ(x)`). -/
def IsLargestMaximizer (m : ℕ) (φ : ℕ → ℝ) (y : ℕ) : Prop :=
  y ∈ Icc 1 m ∧ (∀ x ∈ Icc 1 m, φ x ≤ φ y) ∧ ∀ x ∈ Icc 1 m, y < x → φ x < φ y

end ProductFraming.Trunc


