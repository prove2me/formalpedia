-- Prove2me | Definitions.Def_BoydADMM_Prox_Basic
-- name    : BoydADMM_Prox_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:12.800191+00:00
-- url     : https://prove2.me/theorems/54247349-9a41-4902-8164-1764506e7a69
-- title:
--   Chapter 4 objects: the x-update, prox_{f,ρ}, Π_C, (v)₊, the quadratic f, ‖·‖₁ and S_κ
-- statement:
--   This file fixes the objects of Chapter 4 ("General Patterns") of Boyd, Parikh, Chu, Peleato and Eckstein.
--
--   Vectors live in $\mathbb R^n$ with the Euclidean norm $\|\cdot\|_2$. A matrix $A\in\mathbb R^{p\times n}$ acts on $\mathbb R^n$ in the usual way. An extended-real-valued function $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is described by its effective domain $C=\operatorname{dom} f$ and its finite values on $C$.
--
--   1. **The $x$-update** (p. 25). For $\rho>0$, $A\in\mathbb R^{p\times n}$ and a fixed $v\in\mathbb R^p$, a point $x^+$ is an $x$-update if $x^+\in C$ and
--   $$x^+\in\operatorname*{argmin}_{x\in C}\Bigl(f(x)+\tfrac{\rho}{2}\|Ax-v\|_2^2\Bigr).$$
--   2. **The proximity operator** (§4.1, p. 25). The case $A=I$: $x^+=\mathbf{prox}_{f,\rho}(v)$ means $x^+\in C$ minimizes $f(x)+\tfrac{\rho}{2}\|x-v\|_2^2$ over $C$.
--   3. **Euclidean projection** (p. 26). $x=\Pi_C(v)$ means $x\in C$ and $\|v-x\|_2\le\|v-w\|_2$ for every $w\in C$. This is the published nearest-point predicate `RandomGradFree.Nonsmooth.IsMetricProjection` specialized to $\mathbb R^n$.
--   4. **The nonnegative orthant** $\mathbf R^n_+=\{x\mid x_i\ge 0\ \text{for all } i\}$ and **the nonnegative part** $(v)_+$, the vector with components $\max(v_i,0)$ (p. 26).
--   5. **The quadratic formula** of §4.2 (p. 26): $f(x)=\tfrac12x^TPx+q^Tx+r$ for $P\in\mathbb R^{n\times n}$, $q\in\mathbb R^n$, $r\in\mathbb R$. The book takes $P$ symmetric positive semidefinite, making the quadratic convex. The file also defines the affine set $\{x\mid Fx=g\}$ of §4.2.5 (p. 29).
--   6. **The $\ell_1$ norm** $\|x\|_1=\sum_i|x_i|$ (§4.4.3, p. 32).
--   7. **Soft thresholding** (§4.4.3, p. 32): for $\kappa,a\in\mathbb R$,
--   $$S_\kappa(a)=\begin{cases}a-\kappa & a>\kappa\\ 0 & |a|\le\kappa\\ a+\kappa & a<-\kappa,\end{cases}$$
--   and its componentwise extension $S_\kappa(v)=(S_\kappa(v_1),\dots,S_\kappa(v_n))$.
--
--   These are the objects every closed-form ADMM update of the chapter is stated with.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the $\ell_2$ norm; matrices act through `Matrix.toEuclideanLin`. A function is a pair (domain set, real function); the indicator function of $C$ is the pair $(C, 0)$. `IsXUpdate`, `IsProx` and `IsProjection` are predicates ("$x$ is a minimizer"), not functions, so no choice is made; existence and uniqueness are stated in the theorems. `IsProjection` is an alias of a published general predicate. The quadratic formula is defined for every matrix, while statements invoking the book's convex case require `P.PosSemidef`. In the three-case definition of $S_\kappa$ the cases are disjoint and exhaustive when $\kappa\ge 0$, which is the only case the theorems use.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 25–32, §4 intro, §4.1, §4.2, §4.2.5, §4.4.3 (DOI 10.1561/2200000016)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection

namespace BoydADMM.Prox

/-! Objects of Chapter 4 of Boyd–Parikh–Chu–Peleato–Eckstein (2011), pp. 25–32.

Vectors live in `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the Euclidean norm `‖·‖₂`. A matrix
`A ∈ ℝ^{p×n}` is `A : Matrix (Fin p) (Fin n) ℝ`, acting by `Matrix.toEuclideanLin A`.
An extended-real-valued `f : ℝⁿ → ℝ ∪ {+∞}` is encoded by its effective domain `C = dom f`
and its finite values `f` on `C`; the values of `f` outside `C` are never used. -/

/-- The ADMM `x`-update of Chapter 4 (p. 25):
`x⁺ = argmin_x (f(x) + (ρ/2)‖Ax − v‖₂²)`, where `f` has domain `C`.
`IsXUpdate C f ρ A v x` says that `x ∈ C` and `x` minimizes `f(x) + (ρ/2)‖Ax − v‖₂²` over `C`. -/
def IsXUpdate {n p : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ C ∧ ∀ x' ∈ C,
    f x + (ρ / 2) * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 ≤
      f x' + (ρ / 2) * ‖Matrix.toEuclideanLin A x' - v‖ ^ 2

/-- The proximity operator `prox_{f,ρ}(v)` of §4.1 (p. 25), the case `A = I` of the `x`-update:
`IsProx C f ρ v x` says that `x ∈ C` and `x` minimizes `f(x) + (ρ/2)‖x − v‖₂²` over `C = dom f`. -/
def IsProx {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ) (v x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ C ∧ ∀ x' ∈ C, f x + (ρ / 2) * ‖x - v‖ ^ 2 ≤ f x' + (ρ / 2) * ‖x' - v‖ ^ 2

/-- `x` is a Euclidean projection `Π_C(v)` of `v` onto `C` (p. 26). This is the
published nearest-point predicate, specialized to Boyd et al.'s finite-dimensional space. -/
abbrev IsProjection {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (v x : EuclideanSpace ℝ (Fin n)) : Prop :=
  RandomGradFree.Nonsmooth.IsMetricProjection C v x

/-- The nonnegative orthant `ℝⁿ₊ = {x | x_i ≥ 0 for all i}` (p. 26). -/
def nonnegOrthant (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, 0 ≤ x i}

/-- `(v)₊`, the vector of nonnegative parts `max(v_i, 0)` of the components of `v` (p. 26). -/
noncomputable def posPartVec {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => max (v i) 0)

/-- The quadratic formula of §4.2 (p. 26), `f(x) = (1/2)xᵀPx + qᵀx + r`.
The book's quadratic is convex when `P` is symmetric positive semidefinite; statements
about that setting assume `P.PosSemidef`. -/
noncomputable def quadObj {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (q : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * inner ℝ x (Matrix.toEuclideanLin P x) + inner ℝ q x + r

/-- The affine set `{x | Fx = g}` (§4.2.5, p. 29). -/
def affineSet {n m : ℕ} (F : Matrix (Fin m) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | Matrix.toEuclideanLin F x = g}

/-- The ℓ1 norm `‖x‖₁ = ∑ᵢ |x_i|` (§4.4.3, p. 32). -/
noncomputable def l1Norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, |x i|

/-- The soft thresholding operator `S_κ(a)` (§4.4.3, p. 32), in the book's three-case form:
`a − κ` if `a > κ`, `0` if `|a| ≤ κ`, `a + κ` if `a < −κ`. -/
noncomputable def softThreshold (κ a : ℝ) : ℝ :=
  if κ < a then a - κ else if a < -κ then a + κ else 0

/-- Componentwise soft thresholding of a vector, `(S_κ(v_1), …, S_κ(v_n))` (§4.4.3, p. 32). -/
noncomputable def softThresholdVec {n : ℕ} (κ : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => softThreshold κ (v i))

end BoydADMM.Prox


