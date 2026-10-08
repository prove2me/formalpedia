-- Prove2me | Definitions.Def_TsengBCD_Hemivariate_Setting
-- name    : TsengBCD_Hemivariate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:39.181735+00:00
-- url     : https://prove2.me/theorems/95fbb6f0-d32f-4ff4-ad4f-c9dab66b9da9
-- title:
--   §1, §2, §3, §5, pp. 476–484 — form (1), dom, quasiconvex/hemivariate, coordinatewise minimum (4), the BCD method (2)–(3) and its rules, Assumptions B1–B3, C1, C2
-- statement:
--   This file fixes the objects of §§1–3 and §5 of Tseng (2001).
--
--   **Blocks.** Let $N\ge 1$ and $n_1,\dots,n_N$ be nonnegative integers. A point of $\mathbb R^{n_1+\cdots+n_N}$ is written $x=(x_1,\dots,x_N)$ with coordinate blocks $x_k\in\mathbb R^{n_k}$. We write $(0,\dots,d_k,\dots,0)$ for the vector whose $k$th block is $d_k$ and whose other blocks are zero.
--
--   **Form (1).** The objective is
--   $$f(x_1,\dots,x_N)=f_0(x_1,\dots,x_N)+\sum_{k=1}^N f_k(x_k),$$
--   with $f_0:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ and $f_k:\mathbb R^{n_k}\to\mathbb R\cup\{\infty\}$.
--
--   **Notation (p. 477).** For $h$ with values in $\mathbb R\cup\{\infty\}$, $\operatorname{dom}h=\{x: h(x)<\infty\}$. The level set of $f$ at $x^0$ is $X^0=\{x: f(x)\le f(x^0)\}$. The function $h$ is *quasiconvex* if $h(x+\lambda d)\le\max\{h(x),h(x+d)\}$ for all $x,d$ and $\lambda\in[0,1]$, and *hemivariate* if it is not constant on any (nondegenerate) line segment contained in $\operatorname{dom}h$.
--
--   **Coordinatewise minimum point (4), p. 479.** $z$ is a coordinatewise minimum point of $f$ if $z\in\operatorname{dom}f$ and
--   $$f(z+(0,\dots,d_k,\dots,0))\ge f(z)\qquad\text{for all } d_k\in\mathbb R^{n_k},\ k=1,\dots,N.$$
--
--   **BCD method (2)–(3), p. 478.** Starting from $x^0\in\operatorname{dom}f$, at iteration $r+1$ an index $s\in\{1,\dots,N\}$ is chosen and $x^{r+1}$ is obtained from $x^r$ by minimizing $f$ over block $s$ with the other blocks fixed: $x^{r+1}_s\in\arg\min_{x_s}f(x^r_1,\dots,x^r_{s-1},x_s,x^r_{s+1},\dots,x^r_N)$ and $x^{r+1}_j=x^r_j$ for $j\ne s$. The **essentially cyclic rule** asks for a constant $T\ge N$ such that every index is chosen at least once among any $T$ consecutive iterations; the **cyclic rule** chooses $s=k$ at iterations $k,k+N,k+2N,\dots$.
--
--   **Assumptions of §5, p. 484.**
--   1. (B1) $f_0$ is continuous on $\operatorname{dom}f_0$.
--   2. (B2) For each $k$ and each choice of the other blocks $(x_j)_{j\ne k}$, the function $x_k\mapsto f(x_1,\dots,x_N)$ is quasiconvex and hemivariate.
--   3. (B3) $f_0,f_1,\dots,f_N$ are lower semicontinuous.
--   4. (C1) $\operatorname{dom}f_0$ is open and $f_0$ tends to $\infty$ at every boundary point of $\operatorname{dom}f_0$.
--   5. (C2) $\operatorname{dom}f_0=Y_1\times\cdots\times Y_N$ for some sets $Y_k\subseteq\mathbb R^{n_k}$.
--
--   These are the objects in which Proposition 5.1 and Theorem 5.1 are stated.
--
--   **Formalization Note.** Values in $\mathbb R\cup\{\infty\}$ are `EReal`; the theorems add the standing hypotheses $f_0\ne-\infty$, $f_k\ne-\infty$ everywhere, so $f$ never takes the value $-\infty$ and $f(x)=\infty$ exactly when one summand is $\infty$. Blocks are 0-based: paper block $k\in\{1,\dots,N\}$ is the Lean index $k-1:\mathrm{Fin}\,N$. The product type carries the sup norm of its blocks rather than the Euclidean norm of $\mathbb R^{n_1+\cdots+n_N}$; no statement depends on the choice, since boundedness, convergence, cluster points, continuity and lower semicontinuity agree for equivalent norms. A BCD run is a sequence $x$ with an index sequence $s$, where `s r` is the block chosen at iteration $r+1$; the condition "$x^{r+1}\in\operatorname{dom}f$" follows from minimality and $x^r\in\operatorname{dom}f$. Hemivariance quantifies over segments $[x,y]$ with $x\ne y$, since every function is constant on a one-point segment. In C1, "boundary point" is the topological frontier; the paper's own $\mathrm{bdry}(S)=S\setminus\mathrm{int}(S)$ is empty for an open $S$, but under B3 the two readings agree, because a lower semicontinuous $f_0$ that equals $\infty$ at a frontier point of its open domain tends to $\infty$ there. The positivity of $n_k$ is not required.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), pp. 476–479, (1)–(4), §2, and p. 484, Assumptions B1–B3, C1, C2

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Hemivariate

open Filter Topology

/-- `h` is quasiconvex (p. 477): `h(x + λd) ≤ max{h(x), h(x + d)}` for all `x, d` and `λ ∈ [0, 1]`. -/
def IsQuasiconvex {V : Type*} [AddCommGroup V] [Module ℝ V] (h : V → EReal) : Prop :=
  ∀ x d : V, ∀ t ∈ Set.Icc (0 : ℝ) 1, h (x + t • d) ≤ max (h x) (h (x + d))

/-- `h` is hemivariate (p. 477): `h` is not constant on any (nondegenerate) line segment
contained in `dom h`. -/
def IsHemivariate {V : Type*} [AddCommGroup V] [Module ℝ V] (h : V → EReal) : Prop :=
  ∀ x y : V, x ≠ y → segment ℝ x y ⊆ {p | h p ≠ ⊤} →
    ∃ p ∈ segment ℝ x y, ∃ q ∈ segment ℝ x y, h p ≠ h q

/-- Assumption B1 (p. 484): `f₀` is continuous on `dom f₀`. -/
def AssumptionB1 {N : ℕ} {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal) : Prop :=
  ContinuousOn f0 (TsengBCD.Stationary.dom f0)

/-- Assumption B2 (p. 484): for each block `k` and each value of the other blocks, the function
`x_k ↦ f(x₁, …, x_N)` is quasiconvex and hemivariate. -/
def AssumptionB2 {N : ℕ} {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal) : Prop :=
  ∀ (k : Fin N) (x : TsengBCD.Stationary.X n),
    IsQuasiconvex (fun y => TsengBCD.Stationary.fSum f0 fk (Function.update x k y)) ∧
      IsHemivariate (fun y => TsengBCD.Stationary.fSum f0 fk (Function.update x k y))

/-- Assumption B3 (p. 484): `f₀, f₁, …, f_N` are lower semicontinuous. -/
def AssumptionB3 {N : ℕ} {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal) : Prop :=
  LowerSemicontinuous f0 ∧ ∀ k, LowerSemicontinuous (fk k)

/-- Assumptions B1–B3 together. -/
def AssumptionB {N : ℕ} {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal) : Prop :=
  AssumptionB1 f0 ∧ AssumptionB2 f0 fk ∧ AssumptionB3 f0 fk

/-- Assumption C1 (p. 484): `dom f₀` is open and `f₀` tends to `∞` at every boundary point of
`dom f₀` (boundary read as the topological frontier). -/
def AssumptionC1 {N : ℕ} {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal) : Prop :=
  IsOpen (TsengBCD.Stationary.dom f0) ∧ ∀ z ∈ frontier (TsengBCD.Stationary.dom f0), Tendsto f0 (𝓝 z) (𝓝 ⊤)

/-- Assumption C2 (p. 484): `dom f₀ = Y₁ × ⋯ × Y_N` for some sets `Y_k ⊆ ℜ^{n_k}`. -/
def AssumptionC2 {N : ℕ} {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal) : Prop :=
  ∃ Y : (k : Fin N) → Set (EuclideanSpace ℝ (Fin (n k))), TsengBCD.Stationary.dom f0 = Set.univ.pi Y

end TsengBCD.Hemivariate


