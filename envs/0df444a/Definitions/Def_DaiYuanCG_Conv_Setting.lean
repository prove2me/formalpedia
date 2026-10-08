-- Prove2me | Definitions.Def_DaiYuanCG_Conv_Setting
-- name    : DaiYuanCG_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:49.222109+00:00
-- url     : https://prove2.me/theorems/aa025740-0205-44f3-9218-d235708871e1
-- title:
--   §1–§3, pp. 177–179 — the iteration (1.2)–(1.3), β_k of (2.4), standard and strong Wolfe steps, Algorithm 2.1, Assumption 3.1
-- statement:
--   We minimize a function $f:\mathbb R^n\to\mathbb R$ and write $g(x)=\nabla f(x)$, $g_k=g(x_k)$, $f_k=f(x_k)$ and $y_k=g_{k+1}-g_k$. The inner product of $\mathbb R^n$ is written $u^Td$ and $\|\cdot\|$ is the Euclidean norm. All sequences are indexed from $k=1$.
--
--   1. **Level set.** For a starting point $x_1$, $\mathcal L=\{x\in\mathbb R^n: f(x)\le f(x_1)\}$.
--   2. **Assumption 3.1** (with neighbourhood $\mathcal N$ and constant $L$): $f$ is bounded below on $\mathbb R^n$; $\mathcal N$ is an open set containing $\mathcal L$; $f$ is continuously differentiable in $\mathcal N$; $L>0$ and $$\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|\qquad\text{for all }x,y\in\mathcal N.$$
--   3. **Standard Wolfe step** (conditions (1.7) and (1.10)): a step $\alpha$ along $d$ from $x$ with
--   $$f(x)-f(x+\alpha d)\ge-\delta\alpha\, g(x)^Td,\qquad g(x+\alpha d)^Td>\sigma\, g(x)^Td.$$
--   4. **Strong Wolfe step** (conditions (1.7) and (1.8)): (1.7) together with $|g(x+\alpha d)^Td|\le-\sigma\, g(x)^Td$.
--   5. **The Dai–Yuan coefficient** (2.4): $\beta_k=\|g_{k+1}\|^2/d_k^Ty_k$.
--   6. **The iteration** (1.2)–(1.3) with (2.4): $d_1=-g_1$ and, for every $k\ge1$, $\alpha_k>0$, $x_{k+1}=x_k+\alpha_kd_k$, $d_{k+1}=-g_{k+1}+\beta_kd_k$.
--   7. **A run of Algorithm 2.1**: the iteration in which every step $\alpha_k$ is a standard Wolfe step along $d_k$ from $x_k$. The strong-Wolfe variant of §4 uses strong Wolfe steps instead.
--   8. **The generic method of Lemma 3.2**: any iterates $x_{k+1}=x_k+\alpha_kd_k$ with $\alpha_k>0$, descent directions $g_k^Td_k<0$, and standard Wolfe steps, for every $k\ge1$.
--   9. **(3.7)**: $\liminf_{k\to\infty}\|g_k\|=0$, i.e. for every $\varepsilon>0$ and every $K$ there is $k\ge K$ with $\|g_k\|<\varepsilon$.
--
--   Throughout, the line-search constants satisfy $0<\delta<\sigma<1$; this is a hypothesis of each theorem that needs it, not part of the definitions.
--
--   These objects are the whole vocabulary of the Dai–Yuan convergence analysis: the goal theorem and all milestones are stated in their terms.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $g(x)$ is Mathlib's `gradient f x`. "Continuously differentiable in $\mathcal N$" is encoded as differentiability at every point of the open set $\mathcal N$ together with continuity of $\nabla f$ on $\mathcal N$; the Lipschitz bound holds on $\mathcal N$ only, and neither boundedness of $\mathcal L$ nor global differentiability is assumed. The curvature condition (1.10) is strict, as printed. $\beta_k$ is a Lean division, equal to $0$ when $d_k^Ty_k=0$; along a run $d_k^Ty_k>0$, so that value is never used. Index $0$ of every sequence is unconstrained and never used. Liminf is written in the $\forall\varepsilon\,\forall K\,\exists k\ge K$ form, because the real `Filter.liminf` returns a junk value on unbounded sequences.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), pp. 177–180, (1.2)–(1.3), (1.7), (1.8), (1.10), (2.4), Algorithm 2.1, Assumption 3.1 and (3.1), Lemma 3.2, (3.7), https://doi.org/10.1137/S1052623497318992

import Mathlib

namespace DaiYuanCG.Conv

/-- The space `ℜⁿ` with the Euclidean inner product `gᵀd` and norm `‖·‖`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The level set `ℒ = {x ∈ ℜⁿ : f(x) ≤ f(x₁)}` of Assumption 3.1 (p. 179). -/
def levelSet {n : ℕ} (f : E n → ℝ) (x1 : E n) : Set (E n) :=
  {x | f x ≤ f x1}

/-- Assumption 3.1 (p. 179) at the starting point `x1`, with its neighbourhood `N` of the
level set and its Lipschitz constant `L`:
(1) `f` is bounded below on `ℜⁿ` and continuously differentiable in an open set `N`
containing the level set `ℒ`; (2) `∇f` is Lipschitz on `N` with constant `L > 0`, (3.1). -/
def Assumption31 {n : ℕ} (f : E n → ℝ) (x1 : E n) (N : Set (E n)) (L : ℝ) : Prop :=
  BddBelow (Set.range f) ∧ IsOpen N ∧ levelSet f x1 ⊆ N ∧
    (∀ x ∈ N, DifferentiableAt ℝ f x) ∧ ContinuousOn (gradient f) N ∧
    0 < L ∧ ∀ x ∈ N, ∀ y ∈ N, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- The standard Wolfe conditions (1.7) and (1.10) (p. 178) for the step `α` along `d`
from `x`; the curvature condition (1.10) is strict, as printed. -/
def StdWolfe {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (x d : E n) (α : ℝ) : Prop :=
  -(δ * α * inner ℝ (gradient f x) d) ≤ f x - f (x + α • d) ∧
    σ * inner ℝ (gradient f x) d < inner ℝ (gradient f (x + α • d)) d

/-- The strong Wolfe conditions (1.7) and (1.8) (p. 178). -/
def StrongWolfe {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (x d : E n) (α : ℝ) : Prop :=
  -(δ * α * inner ℝ (gradient f x) d) ≤ f x - f (x + α • d) ∧
    |inner ℝ (gradient f (x + α • d)) d| ≤ -(σ * inner ℝ (gradient f x) d)

/-- The Dai–Yuan coefficient (2.4) (p. 178): `β_k = ‖g_{k+1}‖² / d_kᵀy_k`,
`y_k = g_{k+1} − g_k`. A Lean division: it is `0` when `d_kᵀy_k = 0`. -/
noncomputable def betaDY {n : ℕ} (f : E n → ℝ) (x d : ℕ → E n) (k : ℕ) : ℝ :=
  ‖gradient f (x (k + 1))‖ ^ 2 / inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k))

/-- The iteration (1.2)–(1.3) with `β_k` of (2.4), indexed from `1`: `d₁ = −g₁` and, for
`k ≥ 1`, `α_k > 0`, `x_{k+1} = x_k + α_k d_k`, `d_{k+1} = −g_{k+1} + β_k d_k`.
Index `0` is unconstrained. -/
def IsDYIteration {n : ℕ} (f : E n → ℝ) (x d : ℕ → E n) (α : ℕ → ℝ) : Prop :=
  d 1 = -gradient f (x 1) ∧
    ∀ k, 1 ≤ k → 0 < α k ∧ x (k + 1) = x k + α k • d k ∧
      d (k + 1) = -gradient f (x (k + 1)) + betaDY f x d k • d k

/-- A run of Algorithm 2.1 (p. 179): the iteration with standard Wolfe steps (1.7), (1.10). -/
def IsDYRun {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (x d : ℕ → E n) (α : ℕ → ℝ) : Prop :=
  IsDYIteration f x d α ∧ ∀ k, 1 ≤ k → StdWolfe f δ σ (x k) (d k) (α k)

/-- The iteration of Algorithm 2.1 with strong Wolfe steps (1.7), (1.8) (§4, p. 181). -/
def IsDYRunStrong {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (x d : ℕ → E n) (α : ℕ → ℝ) : Prop :=
  IsDYIteration f x d α ∧ ∀ k, 1 ≤ k → StrongWolfe f δ σ (x k) (d k) (α k)

/-- The generic method of Lemma 3.2 (p. 179): iterates of the form (1.2) with `α_k > 0`,
descent directions `g_kᵀd_k < 0`, and steps satisfying the standard Wolfe conditions. -/
def IsDescentWolfeMethod {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (x d : ℕ → E n) (α : ℕ → ℝ) :
    Prop :=
  ∀ k, 1 ≤ k → 0 < α k ∧ x (k + 1) = x k + α k • d k ∧
    inner ℝ (gradient f (x k)) (d k) < 0 ∧ StdWolfe f δ σ (x k) (d k) (α k)

/-- `liminf_{k→∞} ‖g_k‖ = 0`, (3.7) (p. 180), in the form: for every `ε > 0` and every `K`
there is `k ≥ K` with `‖g_k‖ < ε`. -/
def LiminfGradZero {n : ℕ} (f : E n → ℝ) (x : ℕ → E n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ k ≥ K, ‖gradient f (x k)‖ < ε

end DaiYuanCG.Conv


