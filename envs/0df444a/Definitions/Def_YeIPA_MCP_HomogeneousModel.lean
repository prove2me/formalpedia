-- Prove2me | Definitions.Def_YeIPA_MCP_HomogeneousModel
-- name    : YeIPA_MCP_HomogeneousModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:00.938491+00:00
-- url     : https://prove2.me/theorems/fe3ebaa8-a2f2-42a7-a40d-90331db58859
-- title:
--   Monotone maps on the orthant, scaled Lipschitz (8.21), $R_{++}$, $S_{++}(r)$, $C_{++}(r,\delta)$, the homogeneous map $\psi$ (8.23), the step (8.42)–(8.47)
-- statement:
--   This module defines the objects of §8.4 (the monotone complementarity problem) of Ye's *Interior Point Algorithms*. Vectors in $\mathbb R^N$ are compared componentwise, $e$ is the all-ones vector, $X=\operatorname{diag}(x)$, and $\mathbb R^N_{++}=\{x: x>0\}$ is the open positive orthant. For a map $g:\mathbb R^N\to\mathbb R^N$, $\nabla g(x)$ is its Jacobian at $x$.
--
--   1. **Monotone map**: $g$ is monotone on $\mathbb R^N_{++}$ if $(x^1-x^2)^T(g(x^1)-g(x^2))\ge0$ for all $x^1,x^2>0$.
--   2. **Scaled Lipschitz** (8.21): given $v:(0,1)\to(1,\infty)$ monotone increasing, $g$ is scaled Lipschitz with $v$ if
--   $$\|X(g(x+d)-g(x)-\nabla g(x)d)\|_1\le v(\alpha)\,d^T\nabla g(x)d\quad\text{whenever } d\in\mathbb R^N,\ x\in\mathbb R^N_{++},\ \|X^{-1}d\|_\infty\le\alpha<1.$$
--   3. For $f:\mathbb R^n\to\mathbb R^n$ the **residual set** $R_{++}=\{s-f(x): x>0,\ s>0\}$, the **slice** $S_{++}(r)=\{(x,s)\in\mathbb R^{2n}_{++}: s=f(x)+r\}$ for $r\in\mathbb R^n$, and $C_{++}(r,\delta)=\{(x,y)\in S_{++}(r): x^Ty\le\delta\}$.
--   4. The **homogeneous map** (8.23): for $(x;\tau)\in\mathbb R^{n+1}$ with $x\in\mathbb R^n$, $\tau\in\mathbb R$,
--   $$\psi(x,\tau)=\begin{pmatrix}\tau f(x/\tau)\\ -x^Tf(x/\tau)\end{pmatrix}\in\mathbb R^{n+1}.$$
--   5. The **interior-point step** on $\mathbb R^{n+1}$ (points $x=(x;\tau)$, $s=(s;\kappa)$): $\mu=x^Ts/(n+1)$ and the residual $r=s-\psi(x)$; a pair $(d_x,d_s)$ is a **direction** with parameters $\eta,\gamma$ at $(x,s)$ if
--   $$d_s-\nabla\psi(x)d_x=-\eta r\quad(8.42),\qquad Xd_s+Sd_x=\gamma\mu e-Xs\quad(8.43);$$
--   for a step size $\alpha$ the **new iterate** is $x^+=x+\alpha d_x$ (8.46) and $s^+=s+\alpha d_s+\psi(x^+)-\psi(x)-\alpha\nabla\psi(x)d_x$ (8.47); the Euclidean norm is $\|w\|=(\sum_iw_i^2)^{1/2}$.
--
--   **Formalization Note** Vectors are `Fin N → ℝ` (0-based indices). A point $(x;\tau)$ of $\mathbb R^{n+1}$ is `z : Fin (n+1) → ℝ` with $x$ = `Fin.init z` and $\tau$ = `z (Fin.last n)`; $\psi$ is assembled with `Fin.snoc`. The Jacobian $\nabla g(x)$ is Mathlib's Fréchet derivative `fderiv ℝ g x`, so "$\nabla\psi$" always means the true derivative of $\psi$ (not the block matrix printed in (8.24); see the mission's findings). The book defines $\psi$ only on $\mathbb R^{n+1}_{++}$; the Lean function is total (division by $\tau=0$ gives $0$) but every theorem evaluates $\psi$ and its derivative only at points with $\tau>0$. In (8.21), "monotone increasing" is encoded as `MonotoneOn v (Ioo 0 1)` (nondecreasing) together with $v>1$ on $(0,1)$; $\|X^{-1}d\|_\infty\le\alpha$ is written coordinatewise as $|d_i/x_i|\le\alpha$ and $\alpha$ ranges over $(0,1)$, the domain of $v$. The direction is a predicate (`IsDirection`): any solution of (8.42)–(8.43) is allowed. $s^+$ is defined by the first line of (8.47); its closed form $\psi(x^+)+(1-\alpha\eta)r$ is part of Lemma 8.28 and Theorem 8.29.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 256 ((8.21)), p. 257 (R₊₊, S₊₊(r)), p. 258 (C₊₊), p. 260 ((8.23)), p. 268 ((8.42)–(8.43), rᵏ, μᵏ), p. 269 ((8.46)–(8.47))

import Mathlib

open Matrix

namespace YeIPA.MCP

/-!
# The monotone complementarity problem, the homogeneous map ψ and the central step of §8.4

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997, §8.4: the open orthant, a
monotone map `f` on it and the scaled Lipschitz condition (8.21) p. 256; the residual set `R₊₊`
and the slices `S₊₊(r)` p. 257; `C₊₊(θr, δ)` p. 258 (Lemma 8.21); the homogeneous map
`ψ(x, τ) = (τ f(x/τ); −xᵀ f(x/τ))` (8.23) p. 260; the residual `rᵏ = sᵏ − ψ(xᵏ)`,
`μᵏ = (xᵏ)ᵀsᵏ/(n+1)`, the direction (8.42)–(8.43) p. 268 and the new iterate (8.46)–(8.47)
p. 269.

Vectors are `Fin N → ℝ` (indices `0, …, N-1`); vector inequalities are componentwise; `e` is the
all-ones vector and `X = diag(x)`. A point of `ℝⁿ⁺¹` is `(x; τ)`: its first `n` coordinates
`Fin.init z` are `x` and its last coordinate `z (Fin.last n)` is `τ`. The Jacobian `∇g(x)` of a
map `g` is Mathlib's Fréchet derivative `fderiv ℝ g x`, so `∇g(x) d` is `fderiv ℝ g x d`.
-/

/-- The open orthant `ℝᴺ₊₊ = {x ∈ ℝᴺ : x > 0}` (the book's `R̊ᴺ₊`). -/
def posOrthant (N : ℕ) : Set (Fin N → ℝ) := {x | ∀ i, 0 < x i}

/-- `g` is monotone on the open orthant (§1.3.10, p. 27; §8.4.1, p. 257):
`(x¹ − x²)ᵀ(g(x¹) − g(x²)) ≥ 0` for all `x¹, x² > 0`. -/
def MonotoneOnPos {N : ℕ} (g : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ x₁ ∈ posOrthant N, ∀ x₂ ∈ posOrthant N, 0 ≤ (x₁ - x₂) ⬝ᵥ (g x₁ - g x₂)

/-- The Euclidean norm `‖w‖ = (∑ᵢ wᵢ²)^{1/2}`. -/
noncomputable def norm2 {N : ℕ} (w : Fin N → ℝ) : ℝ := Real.sqrt (∑ i, w i ^ 2)

/-- The scaled Lipschitz condition (8.21), p. 256. `v : (0, 1) → (1, ∞)` is monotone
increasing (nondecreasing on `(0, 1)`, with values `> 1` there), and
`‖X(g(x + d) − g(x) − ∇g(x)d)‖₁ ≤ v(α) dᵀ∇g(x)d` whenever `d ∈ ℝᴺ`, `x ∈ ℝᴺ₊₊` and
`‖X⁻¹d‖_∞ ≤ α < 1` (with `α ∈ (0, 1)`, the domain of `v`). `‖X⁻¹d‖_∞ ≤ α` is written
coordinatewise as `|dᵢ / xᵢ| ≤ α` for every `i`. -/
def ScaledLipschitz {N : ℕ} (g : (Fin N → ℝ) → (Fin N → ℝ)) (v : ℝ → ℝ) : Prop :=
  (∀ α : ℝ, 0 < α → α < 1 → 1 < v α) ∧ MonotoneOn v (Set.Ioo 0 1) ∧
  ∀ x ∈ posOrthant N, ∀ d : Fin N → ℝ, ∀ α : ℝ, 0 < α → α < 1 → (∀ i, |d i / x i| ≤ α) →
    ∑ i, |x i * (g (x + d) i - g x i - fderiv ℝ g x d i)| ≤ v α * (d ⬝ᵥ fderiv ℝ g x d)

/-- The set of residuals `R₊₊ = {s − f(x) ∈ ℝⁿ : (x, s) > 0}` (p. 257). -/
def Rpp {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {r | ∃ x s : Fin n → ℝ, x ∈ posOrthant n ∧ s ∈ posOrthant n ∧ r = s - f x}

/-- `S₊₊(r) = {(x, s) ∈ ℝ²ⁿ₊₊ : s = f(x) + r}` (p. 257). -/
def Spp {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (r : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ posOrthant n ∧ p.2 ∈ posOrthant n ∧ p.2 = f p.1 + r}

/-- `C₊₊(r, δ) = {(x, y) ∈ S₊₊(r) : xᵀy ≤ δ}` (p. 258, Lemma 8.21, used with `r = θr`). -/
def Cpp {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (r : Fin n → ℝ) (δ : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ Spp f r ∧ p.1 ⬝ᵥ p.2 ≤ δ}

/-- The homogeneous map (8.23), p. 260: for `z = (x; τ) ∈ ℝⁿ⁺¹`,
`ψ(x, τ) = (τ f(x/τ); −xᵀ f(x/τ))`. The book defines it on `ℝⁿ⁺¹₊₊`; every theorem evaluates
it there (or uses its derivative there), so the value at `τ ≤ 0` is never used. -/
noncomputable def psi {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ)
    (fun i => z (Fin.last n) * f (fun j => Fin.init z j / z (Fin.last n)) i)
    (-(Fin.init z ⬝ᵥ f (fun j => Fin.init z j / z (Fin.last n))))

/-- `μ = xᵀs/(n + 1)` for `x, s ∈ ℝⁿ⁺¹` (p. 268). -/
noncomputable def mu {n : ℕ} (x s : Fin (n + 1) → ℝ) : ℝ := x ⬝ᵥ s / ((n : ℝ) + 1)

/-- The residual `r = s − ψ(x)` (p. 268). -/
noncomputable def residual {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (x s : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  s - psi f x

/-- `(d_x, d_s)` solves the direction equations at the iterate `(x, s)` (p. 268):
`d_s − ∇ψ(x) d_x = −η r` (8.42) and `X d_s + S d_x = γ μ e − X s` (8.43), with
`r = s − ψ(x)` and `μ = xᵀs/(n + 1)`. -/
def IsDirection {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (η γ : ℝ)
    (x s dx ds : Fin (n + 1) → ℝ) : Prop :=
  ds - fderiv ℝ (psi f) x dx = -(η • residual f x s) ∧
  ∀ i, x i * ds i + s i * dx i = γ * mu x s - x i * s i

/-- The new primal iterate (8.46), p. 269: `x⁺ = x + α d_x`. -/
def newX {n : ℕ} (x dx : Fin (n + 1) → ℝ) (α : ℝ) : Fin (n + 1) → ℝ := x + α • dx

/-- The new dual iterate (8.47), p. 269, first line:
`s⁺ = s + α d_s + ψ(x⁺) − ψ(x) − α ∇ψ(x) d_x`. -/
noncomputable def newS {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (x s dx ds : Fin (n + 1) → ℝ) (α : ℝ) : Fin (n + 1) → ℝ :=
  s + α • ds + psi f (newX x dx α) - psi f x - α • fderiv ℝ (psi f) x dx

end YeIPA.MCP


