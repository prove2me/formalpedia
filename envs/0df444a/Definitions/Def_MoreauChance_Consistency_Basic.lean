-- Prove2me | Definitions.Def_MoreauChance_Consistency_Basic
-- name    : MoreauChance_Consistency_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:21:52.464837+00:00
-- url     : https://prove2.me/theorems/dd624da9-fe74-490e-8338-08bdd15b55d4
-- title:
--   §2.1–§2.2, pp. 3–4 — Moreau envelope, Γ₀(H), coercivity, conjugate, subdifferential, weak convergence, Painlevé–Kuratowski and Mosco convergence
-- statement:
--   This file fixes the convex-analytic vocabulary of §2.1–§2.2 of van Ackooij, Pérez-Aros, Soto and Vilches. Throughout, $\mathcal H$ is a real inner product space (in the theorems: a separable Hilbert space) and $\mathbb R_\infty := \mathbb R\cup\{+\infty\}$.
--
--   1. **Moreau envelope.** For $\psi:\mathcal H\to\mathbb R_\infty$ and $\lambda>0$,
--   $$
--   \mathrm e_\lambda\psi(x) := \inf_{z\in\mathcal H}\Big\{\psi(z)+\frac{1}{2\lambda}\|x-z\|^2\Big\}.
--   $$
--   The infimum is taken in the extended reals, so it is never replaced by a default value.
--   2. **Γ₀(H).** $\psi\in\Gamma_0(\mathcal H)$ means: $\psi$ never takes the value $-\infty$, it is proper ($\operatorname{dom}\psi := \{x:\psi(x)<+\infty\}\neq\emptyset$), convex (its epigraph $\{(x,t):\psi(x)\le t\}$ is convex) and lower semicontinuous.
--   3. **Coercivity.** $\psi$ is coercive if every sublevel set $\{x:\psi(x)\le\alpha\}$, $\alpha\in\mathbb R$, is bounded.
--   4. **Conjugate.** $\psi^*(z) := \sup_{y\in\mathcal H}\{\langle z,y\rangle-\psi(y)\}$.
--   5. **Subdifferential.** $\partial\psi(x) := \{z:\psi(y)\ge\psi(x)+\langle z,y-x\rangle\ \forall y\}$ for $x\in\operatorname{dom}\psi$, and $\partial\psi(x):=\emptyset$ when $\psi(x)=+\infty$.
--   6. **Fréchet differentiability** of an extended-valued $\varphi$ at $u$: $\varphi$ is finite on a neighbourhood of $u$ and the real function it defines there is Fréchet differentiable at $u$.
--   7. **Weak convergence.** $x_k\rightharpoonup x$ iff $\langle x_k,y\rangle\to\langle x,y\rangle$ for every $y\in\mathcal H$. A function $h:\mathcal H\to\mathbb R$ is sequentially weakly continuous if $x_k\rightharpoonup x$ implies $h(x_k)\to h(x)$.
--   8. **Set convergence.** For sets $C_k\subseteq\mathcal H$:
--   $\liminf_k C_k := \{x:\exists x_k\in C_k,\ x_k\to x\}$, $\limsup_k C_k := \{x:\exists x_n\in C_{k_n},\ k_n\to\infty,\ x_n\to x\}$, and $\text{w-}\limsup_k C_k$ is the same with $x_n\rightharpoonup x$. The sequence $(C_k)$ **Painlevé–Kuratowski converges** to $C$ if $C\subseteq\liminf_k C_k$ and $\limsup_k C_k\subseteq C$; it **Mosco converges** to $C$ if $C\subseteq\liminf_k C_k$ and $\text{w-}\limsup_k C_k\subseteq C$.
--
--   These objects are shared by every statement of the mission: the Moreau envelope regularizes both the constraint and the objective of the chance-constrained problem, and the set convergences describe how the regularized feasible sets approach the original one.
--
--   **Formalization Note** Extended-valued functions are `H → EReal` (properness excludes $-\infty$). Convexity of an $\mathbb R_\infty$-valued function is stated through its epigraph, since `EReal` is not a real vector space. Weak convergence is written through inner products (Riesz representation).
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, pp. 3–4, §2.1 Notation and §2.2 (definition of the Moreau envelope)

import Mathlib

open scoped InnerProductSpace
open Filter Topology

namespace MoreauChance.Consistency

/-- Moreau envelope `e_λ f(x) := inf_z { f(z) + ‖x - z‖² / (2λ) }` (p. 4), as an `EReal` infimum.
Meaningful for `0 < lam`; every statement assumes it. -/
noncomputable def moreauEnv {E : Type*} [NormedAddCommGroup E] (f : E → EReal) (lam : ℝ) (x : E) :
    EReal :=
  ⨅ z, f z + ((‖x - z‖ ^ 2 / (2 * lam) : ℝ) : EReal)

/-- Weak convergence `x k ⇀ x0` in a real inner product space. -/
def WeakConv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : ℕ → H) (x0 : H) :
    Prop :=
  ∀ y : H, Tendsto (fun k => ⟪x k, y⟫_ℝ) atTop (𝓝 ⟪x0, y⟫_ℝ)

/-- Sequential weak continuity of a real function: `x k ⇀ x0` implies `h (x k) → h x0`. -/
def SeqWeakCont {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (h : H → ℝ) : Prop :=
  ∀ (x : ℕ → H) (x0 : H), WeakConv x x0 → Tendsto (fun k => h (x k)) atTop (𝓝 (h x0))

/-- `lim inf_k C_k := {x | ∃ x_k ∈ C_k with x_k → x}` (p. 4). -/
def setLiminf {H : Type*} [NormedAddCommGroup H] (Cs : ℕ → Set H) : Set H :=
  {x | ∃ xk : ℕ → H, (∀ k, xk k ∈ Cs k) ∧ Tendsto xk atTop (𝓝 x)}

/-- `lim sup_k C_k := {x | ∃ x_n ∈ C_{k_n} with k_n → ∞ and x_n → x}` (p. 4). -/
def setLimsup {H : Type*} [NormedAddCommGroup H] (Cs : ℕ → Set H) : Set H :=
  {x | ∃ (kn : ℕ → ℕ) (xn : ℕ → H), Tendsto kn atTop atTop ∧ (∀ n, xn n ∈ Cs (kn n)) ∧
    Tendsto xn atTop (𝓝 x)}

/-- `w-lim sup_k C_k := {x | ∃ x_n ∈ C_{k_n} with k_n → ∞ and x_n ⇀ x}` (p. 4). -/
def weakSetLimsup {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Cs : ℕ → Set H) :
    Set H :=
  {x | ∃ (kn : ℕ → ℕ) (xn : ℕ → H), Tendsto kn atTop atTop ∧ (∀ n, xn n ∈ Cs (kn n)) ∧
    WeakConv xn x}

/-- Painlevé–Kuratowski convergence of `C_k` to `C` (p. 4, conditions a) and b)). -/
def PKConv {H : Type*} [NormedAddCommGroup H] (Cs : ℕ → Set H) (C : Set H) : Prop :=
  C ⊆ setLiminf Cs ∧ setLimsup Cs ⊆ C

/-- Mosco convergence of `C_k` to `C` (p. 4, conditions a) and c)). -/
def MoscoConv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Cs : ℕ → Set H)
    (C : Set H) : Prop :=
  C ⊆ setLiminf Cs ∧ weakSetLimsup Cs ⊆ C

/-- `ψ ∈ Γ₀(H)`: `ψ : H → ℝ ∪ {+∞}` (never `⊥`), proper, convex (epigraph) and lower
semicontinuous. -/
def IsGammaZero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (ψ : H → EReal) : Prop :=
  (∀ x, ψ x ≠ ⊥) ∧ (∃ x, ψ x ≠ ⊤) ∧ Convex ℝ {q : H × ℝ | ψ q.1 ≤ (q.2 : EReal)} ∧
    LowerSemicontinuous ψ

/-- Coercive: every sublevel set `{x | ψ x ≤ α}`, `α ∈ ℝ`, is bounded (p. 3). -/
def IsCoercive {H : Type*} [NormedAddCommGroup H] (ψ : H → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded {x | ψ x ≤ (α : EReal)}

/-- Fenchel conjugate `ψ*(z) = sup_y {⟨z, y⟩ − ψ(y)}` (p. 3). -/
noncomputable def conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (ψ : H → EReal)
    (z : H) : EReal :=
  ⨆ y, ((⟪z, y⟫_ℝ : ℝ) : EReal) - ψ y

/-- Convex subdifferential (p. 3); empty where `φ x = +∞`. -/
def subdiff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : H → EReal) (x : H) :
    Set H :=
  {z | φ x ≠ ⊤ ∧ ∀ y, φ x + ((⟪z, y - x⟫_ℝ : ℝ) : EReal) ≤ φ y}

/-- Fréchet differentiability of an extended-real function at `u`: finite near `u`, and the real
function it defines there has a Fréchet derivative at `u`. -/
def FrechetDiffAtE {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : H → EReal)
    (u : H) : Prop :=
  (∀ᶠ w in 𝓝 u, φ w ≠ ⊤ ∧ φ w ≠ ⊥) ∧ ∃ L : H →L[ℝ] ℝ, HasFDerivAt (fun w => (φ w).toReal) L u

end MoreauChance.Consistency


