-- Prove2me | Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty
-- name    : SparseLpLq_SmallP_Supplement_Penalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:09:01.508298+00:00
-- url     : https://prove2.me/theorems/cfa5b0f6-418b-4ffd-af42-6ef96d66309f
-- title:
--   (3.3), Definition C.1, Appendix C — penalty function F_λ, local and ϵ-minimizers, Euclidean dist and projection onto FEA(A,b,σ,1)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $\sigma\ge0$ and $\Phi(x)=\|x\|_p^p$.
--
--   1. **Penalty function** (3.3): for $\lambda>0$,
--   $$F_\lambda(x):=\Phi(x)+\lambda\big(\|Ax-b\|_1-\sigma\big)_+,\qquad (t)_+=\max\{t,0\}.$$
--   2. **Local minimizers.** $x^*$ is a local minimizer of (1.4) if $x^*\in\mathrm{FEA}(A,b,\sigma,1)$ and $\Phi(x^*)\le\Phi(x)$ for every feasible $x$ in some neighbourhood of $x^*$; it is a local minimizer of (3.3) if $F_\lambda(x^*)\le F_\lambda(x)$ for every $x$ in some neighbourhood of $x^*$.
--   3. **$\epsilon$-minimizers** (Definition C.1). $x_\epsilon$ is an $\epsilon$-minimizer of (1.4) if $x_\epsilon\in\mathrm{FEA}(A,b,\sigma,1)$ and $\Phi(x_\epsilon)\le\min\{\Phi(x):x\in\mathrm{FEA}(A,b,\sigma,1)\}+\epsilon$; it is an $\epsilon$-minimizer of (3.3) if $F_\lambda(x_\epsilon)\le\min_{x}F_\lambda(x)+\epsilon$.
--   4. **Distance and projection.** $\mathrm{dist}(x,\mathrm{FEA}(A,b,\sigma,1))$ is the Euclidean distance from $x$ to the feasible set, and $y=\mathcal P_{\mathrm{FEA}(A,b,\sigma,1)}(x)$ when $y$ is a feasible point with $\|x-y\|_2\le\|x-z\|_2$ for every feasible $z$.
--
--   These are the objects of the exact penalty results, Lemma C.3 and Theorems C.1–C.3.
--
--   **Formalization Note** The minima in Definition C.1 are written as bounds against every competitor ($\Phi(x_\epsilon)\le\Phi(y)+\epsilon$ for every feasible $y$, and $F_\lambda(x_\epsilon)\le F_\lambda(y)+\epsilon$ for every $y$), which is equivalent and does not depend on a junk value of an infimum. Neighbourhoods are those of $\mathbb R^n$ (all norms give the same topology). The distance is `Metric.infDist` in `EuclideanSpace ℝ (Fin n)`. The projection is a predicate, not a choice function.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 12, (3.3); pp. 25–27, Theorem C.1 (local minimizers), Definition C.1, Lemma C.3 (dist), Theorem C.3 (projection)

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP

/-! ### Euclidean distance and projection onto `FEA(A,b,σ,1)` (Appendix C) -/

/-- `dist(x, FEA(A,b,σ,1))`, the Euclidean distance (computed in `EuclideanSpace ℝ (Fin n)`). -/
noncomputable def distFEA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    ((fun y : Fin n → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) '' FEA A b σ 1)

/-- `y = 𝒫_{FEA(A,b,σ,1)}(x)`: `y` is a Euclidean nearest point of `FEA(A,b,σ,1)` to `x`. -/
def IsProjFEA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (x y : Fin n → ℝ) : Prop :=
  y ∈ FEA A b σ 1 ∧ ∀ z ∈ FEA A b σ 1, qNorm 2 (x - y) ≤ qNorm 2 (x - z)

/-! ### The penalty problem (3.3) and minimizers (Appendix C) -/

/-- `F_λ(x) := ‖x‖_p^p + λ(‖Ax − b‖₁ − σ)₊` of (3.3). -/
noncomputable def Fpen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ p lam : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  lpObj p x + lam * max (qNorm 1 (A *ᵥ x - b) - σ) 0

/-- `x*` is a local minimizer of problem (1.4): feasible, and `‖x*‖_p^p ≤ ‖x‖_p^p` for every
feasible `x` in a neighbourhood of `x*`. -/
def IsLocalMin14 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ p : ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ FEA A b σ 1 ∧ ∀ᶠ y in 𝓝 x, y ∈ FEA A b σ 1 → lpObj p x ≤ lpObj p y

/-- `x*` is a local minimizer of the penalty problem (3.3). -/
def IsLocalMinPen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ p lam : ℝ)
    (x : Fin n → ℝ) : Prop :=
  ∀ᶠ y in 𝓝 x, Fpen A b σ p lam x ≤ Fpen A b σ p lam y

/-- Definition C.1(i): `x` is an `ϵ`-minimizer of (1.4): `x ∈ FEA(A,b,σ,1)` and
`‖x‖_p^p ≤ ‖y‖_p^p + ϵ` for every feasible `y`. -/
def IsEpsMin14 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ p ε : ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ FEA A b σ 1 ∧ ∀ y ∈ FEA A b σ 1, lpObj p x ≤ lpObj p y + ε

/-- Definition C.1(ii): `x` is an `ϵ`-minimizer of (3.3): `F_λ(x) ≤ F_λ(y) + ϵ` for every `y`. -/
def IsEpsMinPen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ p lam ε : ℝ)
    (x : Fin n → ℝ) : Prop :=
  ∀ y, Fpen A b σ p lam x ≤ Fpen A b σ p lam y + ε

end SparseLpLq.SmallP.Supplement


