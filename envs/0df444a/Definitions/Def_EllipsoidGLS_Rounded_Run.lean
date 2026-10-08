-- Prove2me | Definitions.Def_EllipsoidGLS_Rounded_Run
-- name    : EllipsoidGLS_Rounded_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:59:39.100795+00:00
-- url     : https://prove2.me/theorems/7dcd963a-11c9-4118-8f17-3580c68bd321
-- title:
--   §2 (1)–(9), (22)–(23), pp. 173–175 — the rounded ellipsoid method with a weak separation oracle: N, δ, p, the update, runs, and K_k
-- statement:
--   The ellipsoid method with rounding, as specified by Grötschel, Lovász and Schrijver. Let $n\ge 2$, let $K\subseteq\mathbb{R}^n$ be a convex body with $S(a_0,r)\subseteq K\subseteq S(a_0,R)$, let $c\in\mathbb{R}^n$ be the objective vector and $\varepsilon>0$ the accuracy. All norms are Euclidean.
--
--   **Constants.** With $\log$ the natural logarithm,
--   $$N = 4n^2\left\lceil \log\frac{2R^2\|c\|}{r\varepsilon}\right\rceil,\qquad \delta = \frac{R^2\,4^{-N}}{300n},\qquad p = 5N .$$
--
--   **One step.** Given a centre $x\in\mathbb{R}^n$, a matrix $A$ and a cut vector $a$, put
--   $$b = \frac{Aa}{\sqrt{a^{\mathsf T}Aa}},\qquad x^* = x+\frac{1}{n+1}\,b,\qquad A^* = \frac{2n^2+3}{2n^2}\left(A-\frac{2}{n+1}\,bb^{\mathsf T}\right).$$
--
--   **Runs.** A run with oracle precision $\delta$ and rounding precision $p$ for $N$ steps consists of centres $x_0,x_1,\dots$, matrices $A_0,A_1,\dots$, a set of *feasible indices*, cut vectors $a_k$ and separating vectors $d_k$ such that $x_0=a_0$, $A_0=R^2I$, and for every $k<N$:
--
--   1. **Oracle.** Either $k$ is feasible, $x_k\in S(K,\delta)$ and $a_k=c$; or $k$ is infeasible, $\|d_k\|\ge 1$,
--   $$d_k^{\mathsf T}y\le d_k^{\mathsf T}x_k+\delta\quad\text{for all } y\in K,$$
--   and $a_k=-d_k$.
--   2. **Rounding.** Every entry of $x_{k+1}$ differs from the corresponding entry of $x_k^*$ (computed from $x_k,A_k,a_k$) by at most $2^{-p}$, every entry of $A_{k+1}$ differs from that of $A_k^*$ by at most $2^{-p}$, and $A_{k+1}$ is symmetric.
--
--   **The sets $K_k$.** For $k\ge 0$,
--   $$K_k = \{\,y\in K : c^{\mathsf T}y\ge c^{\mathsf T}x_j \text{ for every feasible } j<k\,\},$$
--   which is $K\cap\{y : c^{\mathsf T}y\ge\zeta_k\}$ with $\zeta_k=\max\{c^{\mathsf T}x_j : 0\le j<k,\ j\text{ feasible}\}$, and is $K$ itself when no $j<k$ is feasible.
--
--   The run is the object about which the mission's lemmas and its main theorem are stated: the theorems hold for every run, whatever valid answers the oracle gives and however the rounding is carried out.
--
--   **Formalization Note** Three generalizations of the page, each of which makes every theorem stated over runs stronger, and none of which the paper's proof goes beyond: (i) the oracle's answers are any answers valid for the specification (1)/(5), chosen step by step, rather than the output of one fixed subroutine SEP; (ii) "rounding to $p$ binary digits behind the point, taking care that $A_{k+1}$ is symmetric" is modelled as any symmetric value within $2^{-p}$ entrywise, which covers nearest rounding and truncation; the proof uses only the consequences $\|A_{k+1}-A_k^*\|\le n2^{-p}$ and $\|x_{k+1}-x_k^*\|\le\sqrt n\,2^{-p}$; (iii) vectors are real, so the oracle's rational input becomes a real one. $N$ uses `Real.log` and `Nat.ceil`, and $4^{-N}$, $2^{-p}$ are integer powers of reals. $A^{-1}$ is never used in the run itself; $b$ divides by $\sqrt{a^{\mathsf T}Aa}$, which is positive along a run because $A_k$ is positive definite (Lemma (2.1)) and $\|a_k\|\ge 1$. $\zeta_k$ is not formed with a supremum, because the real supremum of the empty set is $0$ in Lean.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), pp. 173–174, §2 (1)–(9); p. 175, (22)–(23)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic

namespace EllipsoidGLS.Rounded

open Matrix

/-- (2), p. 173: the number of steps `N = 4n²⌈log(2R²‖c‖/(rε))⌉` (natural logarithm,
Euclidean norm). -/
noncomputable def itN (n : ℕ) (R r ε : ℝ) (c : Fin n → ℝ) : ℕ :=
  4 * n ^ 2 * ⌈Real.log (2 * R ^ 2 * euclNorm c / (r * ε))⌉₊

/-- (3), p. 173: the oracle precision `δ = R²4^{−N}/(300n)`. -/
noncomputable def itDelta (n N : ℕ) (R : ℝ) : ℝ :=
  R ^ 2 * (4 : ℝ) ^ (-(N : ℤ)) / (300 * n)

/-- (4), p. 173: the rounding precision `p = 5N` (binary digits). -/
def itP (N : ℕ) : ℕ := 5 * N

/-- (6), p. 173: `b = A a / √(aᵀ A a)`. -/
noncomputable def bvec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Fin n → ℝ :=
  (Real.sqrt (a ⬝ᵥ A.mulVec a))⁻¹ • A.mulVec a

/-- (7), p. 173: the unrounded next centre `x* = x + b/(n+1)`. -/
noncomputable def xstar {n : ℕ} (x : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Fin n → ℝ :=
  x + (1 / ((n : ℝ) + 1)) • bvec A a

/-- (8), p. 173: the unrounded next matrix
`A* = ((2n²+3)/(2n²)) (A − (2/(n+1)) b bᵀ)`. -/
noncomputable def Astar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((2 * (n : ℝ) ^ 2 + 3) / (2 * (n : ℝ) ^ 2)) •
    (A - (2 / ((n : ℝ) + 1)) • vecMulVec (bvec A a) (bvec A a))

/-- A run of the rounded ellipsoid method of §2 (pp. 173–174), steps `0, …, N − 1`, with
oracle precision `δ` and rounding precision `p`. `x k`, `A k` are the centres and matrices,
`feas k` says that `k` is a feasible index, `a k` is the cut vector used in step `k` and
`d k` the oracle's separating vector at an infeasible index.

* `x₀ = a₀`, `A₀ = R² I`;
* oracle, (1)/(5): either `k` is feasible, `x_k ∈ S(K, δ)` and `a_k = c`; or `k` is
  infeasible, `‖d_k‖ ≥ 1`, `d_kᵀ y ≤ d_kᵀ x_k + δ` for every `y ∈ K`, and `a_k = −d_k`;
* rounding, (9): every entry of `x_{k+1}` and `A_{k+1}` is within `2^{−p}` of the
  corresponding entry of `x_k*`, `A_k*`, and `A_{k+1}` is symmetric. -/
def IsRoundedRun {n : ℕ} (K : Set (Fin n → ℝ)) (c a₀ : Fin n → ℝ) (R δ : ℝ) (p N : ℕ)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ) : Prop :=
  x 0 = a₀ ∧ A 0 = R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) ∧
  ∀ k < N,
    ((feas k ∧ x k ∈ nbhd K δ ∧ a k = c) ∨
      (¬ feas k ∧ 1 ≤ euclNorm (d k) ∧ (∀ y ∈ K, d k ⬝ᵥ y ≤ d k ⬝ᵥ x k + δ) ∧
        a k = -d k)) ∧
    (∀ i, |x (k + 1) i - xstar (x k) (A k) (a k) i| ≤ (2 : ℝ) ^ (-(p : ℤ))) ∧
    (∀ i j, |A (k + 1) i j - Astar (A k) (a k) i j| ≤ (2 : ℝ) ^ (-(p : ℤ))) ∧
    (A (k + 1)).IsSymm

/-- (22)–(23), p. 175: `K_k = K ∩ {x | cᵀx ≥ ζ_k}` with
`ζ_k = max {cᵀx_j | 0 ≤ j < k, j feasible}`, written as "`cᵀy ≥ cᵀx_j` for every feasible
`j < k`". With no feasible `j < k` this is `K` itself. -/
def Kk {n : ℕ} (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (feas : ℕ → Prop) (k : ℕ) : Set (Fin n → ℝ) :=
  {y | y ∈ K ∧ ∀ j < k, feas j → c ⬝ᵥ x j ≤ c ⬝ᵥ y}

end EllipsoidGLS.Rounded


