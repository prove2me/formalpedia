-- Prove2me | Definitions.Def_MifflinSemismooth_Optimality_Setting
-- name    : MifflinSemismooth_Optimality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:26.091397+00:00
-- url     : https://prove2.me/theorems/77a858ae-41a7-418c-870a-7afd15e0065a
-- title:
--   §5, pp. 17–18 — feasibility, optimality, the map M, stationarity, h = max hᵢ and the active set A(x)
-- statement:
--   Mifflin's §5 considers the problem
--   $$
--   \text{minimize } f(x)\quad\text{subject to } h(x)\le 0,
--   $$
--   for functions $f,h:\mathbb R^n\to\mathbb R$, where in the paper $h(x)=\max_{1\le i\le m}h_i(x)$.
--
--   1. $x$ is **feasible** if $h(x)\le 0$ and **strictly feasible** if $h(x)<0$.
--   2. $\bar x$ is **optimal** if $\bar x$ is feasible and $f(\bar x)\le f(x)$ for all feasible $x$.
--   3. The point-to-set map $M:\mathbb R^n\to 2^{\mathbb R^n}$ is
--   $$
--   M(x)=\begin{cases}\partial f(x) & \text{if } h(x)<0,\\ \operatorname{conv}\{\partial f(x)\cup\partial h(x)\} & \text{if } h(x)=0,\\ \partial h(x) & \text{if } h(x)>0.\end{cases}
--   $$
--   4. $\bar x$ is **stationary** if $h(\bar x)\le 0$ and $0\in M(\bar x)$.
--   5. For functions $h_1,\dots,h_m$ ($m\ge 1$), $h(x)=\max_{1\le i\le m}h_i(x)$, and the **active index set** is $A(x)=\{i\in\{1,\dots,m\}: h(x)=h_i(x)\}$.
--
--   These are the objects of the necessary condition (Theorem 7) and the sufficient condition (Theorem 9) of §5.
--
--   **Formalization Note** $\partial$ is the generalized gradient `genGrad` of the shared module `MifflinSemismooth.Extremal.Basic`; $\operatorname{conv}$ is Mathlib's `convexHull`, the plain convex hull of the union. Feasibility, optimality, $M$ and stationarity are defined for an arbitrary $h$; the paper's $h=\max_i h_i$ is `maxConstraint`, a finite maximum over `Fin m` with $m\ge 1$ (`NeZero m`), which is implicit in "$h_1,h_2,\dots,h_m$" and "$\max_{1\le i\le m}$". Indices run over `Fin m`, i.e. $0,\dots,m-1$ instead of $1,\dots,m$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), pp. 17–18, §5: problem, feasibility, optimality, A(x) (p. 17); the map M and stationarity (p. 18)

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §5, p. 17: `x` is feasible if `h(x) ≤ 0`. -/
def IsFeasible {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  h x ≤ 0

/-- Mifflin (1976), §5, p. 17: `x` is strictly feasible if `h(x) < 0`. -/
def IsStrictlyFeasible {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  h x < 0

/-- Mifflin (1976), §5, p. 17: `x̄` is optimal if `x̄` is feasible and `f(x̄) ≤ f(x)` for all
feasible `x`. -/
def IsOptimal {n : ℕ} (f h : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsFeasible h xbar ∧ ∀ x, IsFeasible h x → f xbar ≤ f x

/-- Mifflin (1976), §5, p. 18: the point-to-set map
`M(x) = ∂f(x)` if `h(x) < 0`, `conv (∂f(x) ∪ ∂h(x))` if `h(x) = 0`, `∂h(x)` if `h(x) > 0`. -/
noncomputable def Mmap {n : ℕ} (f h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  if h x < 0 then MifflinSemismooth.Extremal.genGrad f x
  else if h x = 0 then convexHull ℝ (MifflinSemismooth.Extremal.genGrad f x ∪ MifflinSemismooth.Extremal.genGrad h x)
  else MifflinSemismooth.Extremal.genGrad h x

/-- Mifflin (1976), §5, p. 18: `x̄` is stationary if `h(x̄) ≤ 0` and `0 ∈ M(x̄)`. -/
def IsStationary {n : ℕ} (f h : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  h xbar ≤ 0 ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ Mmap f h xbar

/-- Mifflin (1976), §5, p. 17: the constraint function `h(x) = max_{1 ≤ i ≤ m} hᵢ(x)`. -/
noncomputable def maxConstraint {n m : ℕ} [NeZero m] (hs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => hs i x)

/-- Mifflin (1976), §5, p. 17: the active index set `A(x) = {i : h(x) = hᵢ(x)}`. -/
def activeIdx {n m : ℕ} [NeZero m] (hs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (Fin m) :=
  {i | maxConstraint hs x = hs i x}

end MifflinSemismooth.Optimality


