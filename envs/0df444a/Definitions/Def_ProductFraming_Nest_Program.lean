-- Prove2me | Definitions.Def_ProductFraming_Nest_Program
-- name    : ProductFraming_Nest_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:21.423436+00:00
-- url     : https://prove2.me/theorems/4b37836b-373e-4954-94b9-e3084b4277aa
-- title:
--   The bound-revealing programs (5) and (6)
-- statement:
--   Fix $m\ge1$. The variable $\Lambda:[m]\to\mathbb R$ plays the role of a tail function $\Lambda(x)=\mathbb P[X\ge x]$, with $\Lambda(m+1)=0$; its law is $\lambda(x)=\Lambda(x)-\Lambda(x+1)$, and $\mathbb E[\min(X,x)]=\sum_{y=1}^{x}\Lambda(y)$.
--
--   1. $\Lambda$ is **feasible for (6)** if $1=\Lambda(1)\ge\Lambda(2)\ge\dots\ge\Lambda(m)\ge0$ and
--   $$\Lambda(x+1)\sum_{y=1}^{m}\Lambda(y)\ \ge\ \sum_{y=x+1}^{m}\Lambda(y),\qquad x=1,\dots,m-1$$
--   (the NBUE property).
--   2. $(U,\Lambda)$ is **feasible for (5)** if $\Lambda$ is feasible for (6), $U(x)\le U(x+1)$ and $U(x)/x\ge U(x+1)/(x+1)$ for $x=1,\dots,m-1$, $\mathbb E[U(X)]=\sum_{x\in[m]}\lambda(x)U(x)=1$, and $U(x)\ge0$ for $x\in[m]$.
--   3. The objective of (5) is $J(U,\Lambda)=\max_{x\in[m]}\frac{U(x)}{x}\,\mathbb E[\min(X,x)]$, and $\gamma$ is its minimum over the feasible set.
--   4. The objective of (6) is
--   $$\mathbb E\Big[\frac{X}{\mathbb E[\min(X,Y)\mid X]}\Big]=\sum_{x\in[m]}\lambda(x)\,\frac{x}{\mathbb E[\min(X,x)]},$$
--   where $Y$ is independent of $X$ with the same law.
--
--   Program (5) is the worst case of the lower bound of Proposition 1 relative to the upper bound of Theorem 2; its optimal value is the approximation ratio of NEST.
--
--   **Formalization Note** `Λ : ℕ → ℝ` and `U : ℕ → ℝ` are used only on $[1,m]$; $\lambda(m)=\Lambda(m)$ encodes $\Lambda(m+1)=0$. The page writes the fifth constraint of (5) as "$\mathbb E[U(x)]=1$", a typo for $\mathbb E[U(X)]=1$. $J$ is a `Finset.sup'` over $[1,m]$, which needs $m\ge1$. $\gamma$ is not defined as a constant: the statements say "the minimum is attained" with `IsLeast`.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §4.3, p. 10, (5) and (6)

import Mathlib

namespace ProductFraming.Nest

open Finset

/-! The bound-revealing programs (5) and (6) of Gallego, Li, Truong, Wang (2020), authors' accepted
manuscript, §4.3, p. 10. The variable `Λ : ℕ → ℝ` is a tail function `Λ(x) = P[X ≥ x]` on `[1, m]`
(only its values there are used), with `Λ(m + 1) = 0`; the law is `λ(x) = Λ(x) − Λ(x + 1)` and
`E[min(X, x)] = ∑_{y=1}^{x} Λ(y)`. -/

/-- `λ(x) = Λ(x) − Λ(x + 1)`, with the convention `Λ(m + 1) = 0`. -/
def lamOf (m : ℕ) (Λ : ℕ → ℝ) (x : ℕ) : ℝ :=
  Λ x - if x + 1 ≤ m then Λ (x + 1) else 0

/-- `E[min(X, x)] = ∑_{y=1}^{x} Λ(y)` for the law with tail `Λ`. -/
def EminTail (Λ : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ y ∈ Icc 1 x, Λ y

/-- The constraints of (6), which are the first two constraints of (5):
`1 = Λ(1) ≥ Λ(2) ≥ ⋯ ≥ Λ(m) ≥ 0` and the NBUE constraint
`Λ(x + 1) · ∑_{y=1}^{m} Λ(y) ≥ ∑_{y=x+1}^{m} Λ(y)` for `x = 1, …, m − 1`. -/
def Feasible6 (m : ℕ) (Λ : ℕ → ℝ) : Prop :=
  Λ 1 = 1 ∧ (∀ x, 1 ≤ x → x < m → Λ (x + 1) ≤ Λ x) ∧ 0 ≤ Λ m ∧
  ∀ x, 1 ≤ x → x < m → ∑ y ∈ Icc (x + 1) m, Λ y ≤ Λ (x + 1) * ∑ y ∈ Icc 1 m, Λ y

/-- The constraints of (5): `Λ` feasible for (6), `U(x) ≤ U(x + 1)` and `U(x)/x ≥ U(x + 1)/(x + 1)`
for `x = 1, …, m − 1`, `E[U(X)] = ∑_{x ∈ [m]} λ(x) U(x) = 1`, and `U(x) ≥ 0` for `x ∈ [m]`. -/
def Feasible5 (m : ℕ) (U Λ : ℕ → ℝ) : Prop :=
  Feasible6 m Λ ∧
  (∀ x, 1 ≤ x → x < m → U x ≤ U (x + 1)) ∧
  (∀ x, 1 ≤ x → x < m → U (x + 1) / ((x : ℝ) + 1) ≤ U x / (x : ℝ)) ∧
  ∑ x ∈ Icc 1 m, lamOf m Λ x * U x = 1 ∧
  ∀ x ∈ Icc 1 m, 0 ≤ U x

/-- The objective of (5): `max_{x ∈ [m]} (U(x)/x) E[min(X, x)]`. -/
noncomputable def J5 {m : ℕ} (hm : 1 ≤ m) (U Λ : ℕ → ℝ) : ℝ :=
  (Icc 1 m).sup' ⟨1, mem_Icc.mpr ⟨le_refl 1, hm⟩⟩ (fun x => U x / (x : ℝ) * EminTail Λ x)

/-- The objective of (6): `E[X / E[min(X, Y) | X]] = ∑_{x ∈ [m]} λ(x) x / E[min(X, x)]`, for `Y`
independent of `X` with the same law. -/
noncomputable def ratio6 (m : ℕ) (Λ : ℕ → ℝ) : ℝ :=
  ∑ x ∈ Icc 1 m, lamOf m Λ x * (x : ℝ) / EminTail Λ x

end ProductFraming.Nest


