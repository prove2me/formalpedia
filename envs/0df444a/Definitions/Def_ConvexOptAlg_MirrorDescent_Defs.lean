-- Prove2me | Definitions.Def_ConvexOptAlg_MirrorDescent_Defs
-- name    : ConvexOptAlg_MirrorDescent_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:41:19.126198+00:00
-- url     : https://prove2.me/theorems/4a0cf007-ee5c-4a4d-841b-492058d4eed0
-- title:
--   Ch. 4 preamble, §4.1, (4.2)–(4.3), (4.6) — Bregman divergence, mirror maps, Bregman projection, mirror descent and dual averaging runs
-- statement:
--   Throughout, $E$ is a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$ (the book's $\mathbb R^n$ with an arbitrary norm). Linear functionals $g$ on $E$ carry the dual norm $\|g\|_*=\sup_{\|x\|\le1}g(x)$, and the book's pairing $g^\top x$ is $g(x)$. A function $\Phi$ comes with an explicit gradient map $x\mapsto\nabla\Phi(x)$, a linear functional on $E$.
--
--   1. **Bregman divergence.** $D_\Phi(x,y)=\Phi(x)-\Phi(y)-\nabla\Phi(y)^\top(x-y)$.
--   2. **Mirror map.** Let $\mathcal D\subseteq E$ be a convex open set. $\Phi:\mathcal D\to\mathbb R$ is a mirror map if (i) $\Phi$ is strictly convex and differentiable on $\mathcal D$ with gradient $\nabla\Phi(x)$; (ii) the gradient takes all possible values, $\nabla\Phi(\mathcal D)=E^*$; (iii) the gradient diverges on the boundary of $\mathcal D$: $\|\nabla\Phi(x)\|_*\to+\infty$ as $x\to z$ within $\mathcal D$, for every boundary point $z$ of $\mathcal D$.
--   3. **Standing setting of Chapter 4.** $\mathcal X$ is compact and convex, $\Phi$ is a mirror map on $\mathcal D$, $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\neq\emptyset$.
--   4. **Subgradient.** A linear functional $g$ is a subgradient of $f$ at $x$ (relative to $\mathcal X$) if $f(x)-f(y)\le g^\top(x-y)$ for every $y\in\mathcal X$.
--   5. **$\rho$-strong convexity of the mirror map** on $\mathcal X\cap\mathcal D$: for all $x,y\in\mathcal X\cap\mathcal D$,
--   $$\Phi(x)-\Phi(y)\le\nabla\Phi(x)^\top(x-y)-\frac{\rho}{2}\|x-y\|^2 .$$
--   6. **Bregman projection.** $z=\Pi^\Phi_{\mathcal X}(y)$ means $z\in\mathcal X\cap\mathcal D$ and $D_\Phi(z,y)\le D_\Phi(x,y)$ for every $x\in\mathcal X\cap\mathcal D$.
--   7. **Mirror descent run** with step $\eta$ for the steps $t=1,\dots,T$: $x_1\in\operatorname{argmin}_{x\in\mathcal X\cap\mathcal D}\Phi(x)$ and, for $1\le t\le T$, $g_t$ is a subgradient of $f$ at $x_t$, $y_{t+1}\in\mathcal D$ satisfies
--   $$\nabla\Phi(y_{t+1})=\nabla\Phi(x_t)-\eta g_t,$$
--   and $x_{t+1}=\Pi^\Phi_{\mathcal X}(y_{t+1})$.
--   8. **Dual averaging run** with step $\eta$ for the steps $t=1,\dots,T$: for $1\le t\le T+1$,
--   $$x_t\in\operatorname*{argmin}_{x\in\mathcal X\cap\mathcal D}\ \eta\sum_{s=1}^{t-1}g_s^\top x+\Phi(x),$$
--   and for $1\le t\le T$, $g_t$ is a subgradient of $f$ at $x_t$.
--
--   These are the objects of Chapter 4 of the book: mirror descent (Section 4.2) and its lazy variant, dual averaging (Section 4.4). Every rate statement of the mission quantifies over all runs, with any choice of subgradient, dual point and minimizer.
--
--   **Formalization Note** The gradient $\nabla\Phi(x)$ is an explicit map `Φ' : E → E →L[ℝ] ℝ` with `HasFDerivAt Φ (Φ' x) x` on $\mathcal D$; only the values of $\Phi$ and $\nabla\Phi$ on $\mathcal D$ matter. The dual norm is the operator norm on `E →L[ℝ] ℝ`. Sequences are indexed from $1$ (index $0$ is unused). Strong convexity of $\Phi$ is stated with the gradient, the form the book's proofs use; the preamble's subgradient form implies it. Dual averaging is encoded by its closed form (4.6), as the book does.
-- source:
--   Bubeck, arXiv:1405.4980v2, Ch. 4 preamble, p. 297; §4.1, p. 298; Eqs. (4.2)–(4.3), p. 299; Eq. (4.6), p. 303; Definition 1.2, p. 235

import Mathlib

namespace ConvexOptAlg.MirrorDescent

/-- Bubeck, Ch. 4 preamble, p. 297: the Bregman divergence
`D_Φ(x, y) = Φ(x) − Φ(y) − ∇Φ(y)ᵀ(x − y)`. The gradient `∇Φ(y)` is the explicit map `Φ' y`, a
continuous linear functional on `E` (the book's `∇Φ(y)ᵀv` is `Φ' y v`). -/
def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (x y : E) : ℝ :=
  Φ x - Φ y - Φ' y (x - y)

/-- Bubeck, §4.1, p. 298: `Φ : D → ℝ` is a mirror map on the convex open set `D` if
(i) `Φ` is strictly convex and differentiable on `D`, with gradient `Φ' x` at every `x ∈ D`;
(ii) the gradient takes all possible values, `∇Φ(D) = ℝⁿ` (every continuous linear functional is
`Φ' y` for some `y ∈ D`);
(iii) the gradient diverges on the boundary of `D`: `‖∇Φ(x)‖ → +∞` as `x → z ∈ ∂D` within `D`.
Only the values of `Φ` and `Φ'` on `D` matter. -/
def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) : Prop :=
  IsOpen D ∧ Convex ℝ D ∧ StrictConvexOn ℝ D Φ ∧
    (∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) ∧
    (∀ φ : E →L[ℝ] ℝ, ∃ y ∈ D, Φ' y = φ) ∧
    (∀ z ∈ frontier D, Filter.Tendsto (fun x => ‖Φ' x‖) (nhdsWithin z D) Filter.atTop)

/-- Bubeck, Ch. 4 preamble (p. 297) and §4.1 (p. 298): the standing setting of the chapter. `X` is a
compact convex set, `Φ` is a mirror map on the convex open set `D`, `X` is included in the closure
of `D`, and `X ∩ D ≠ ∅`. -/
def IsMirrorSetting {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧ IsMirrorMap D Φ Φ' ∧ X ⊆ closure D ∧ (X ∩ D).Nonempty

/-- Bubeck, Definition 1.2 (p. 235) in the dual-norm setting of Ch. 4: the continuous linear
functional `g` is a subgradient of `f` at `x` relative to `X` if `f(x) − f(y) ≤ gᵀ(x − y)` for every
`y ∈ X`. -/
def IsSubgradientOnN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ X, f x - f y ≤ g (x - y)

/-- Bubeck, Ch. 4 preamble (iii), p. 297, for the differentiable mirror map: `Φ` is `ρ`-strongly
convex on `X ∩ D` w.r.t. `‖·‖` if
`Φ(x) − Φ(y) ≤ ∇Φ(x)ᵀ(x − y) − (ρ/2)‖x − y‖²` for all `x, y ∈ X ∩ D`. -/
def IsStronglyConvexMirror {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (ρ : ℝ) : Prop :=
  ∀ x ∈ X ∩ D, ∀ y ∈ X ∩ D, Φ x - Φ y ≤ Φ' x (x - y) - ρ / 2 * ‖x - y‖ ^ 2

/-- Bubeck, §4.1, p. 298: `z` is the Bregman projection `Π^Φ_X(y) = argmin_{x ∈ X ∩ D} D_Φ(x, y)`,
i.e. `z ∈ X ∩ D` and `D_Φ(z, y) ≤ D_Φ(x, y)` for every `x ∈ X ∩ D`. -/
def IsBregmanProjection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (y z : E) : Prop :=
  z ∈ X ∩ D ∧ ∀ x ∈ X ∩ D, bregman Φ Φ' z y ≤ bregman Φ Φ' x y

/-- Bubeck, §4.2, (4.2)–(4.3), p. 299: `(x, y, g)` is a run of mirror descent on `f` with step `η`
for the steps `t = 1, …, T`. The first iterate `x 1 ∈ argmin_{x ∈ X ∩ D} Φ(x)` (index `0` is
unused); at every step `1 ≤ t ≤ T`, `g t` is a subgradient of `f` at `x t` (any one),
`y (t+1) ∈ D` satisfies `∇Φ(y_{t+1}) = ∇Φ(x_t) − η g_t` (4.2), and `x (t+1)` is the Bregman
projection `Π^Φ_X(y_{t+1})` (4.3). -/
def IsMirrorDescentRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (f : E → ℝ) (η : ℝ)
    (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) : Prop :=
  x 1 ∈ X ∩ D ∧ (∀ z ∈ X ∩ D, Φ (x 1) ≤ Φ z) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ T →
      IsSubgradientOnN X f (x t) (g t) ∧
      y (t + 1) ∈ D ∧
      Φ' (y (t + 1)) = Φ' (x t) - η • g t ∧
      IsBregmanProjection X D Φ Φ' (y (t + 1)) (x (t + 1))

/-- Bubeck, §4.4, (4.6), p. 303: `(x, g)` is a run of dual averaging (lazy mirror descent) on `f`
with step `η` for the steps `t = 1, …, T`: for every `1 ≤ t ≤ T + 1`, the iterate
`x t ∈ argmin_{x ∈ X ∩ D} η ∑_{s=1}^{t−1} g_sᵀx + Φ(x)` (so `x 1` minimizes `Φ` on `X ∩ D`), and
for every `1 ≤ t ≤ T`, `g t` is a subgradient of `f` at `x t` (any one). The sum over `s < t` is
written `∑ s ∈ Finset.Ico 1 t`. -/
def IsDualAveragingRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (f : E → ℝ) (η : ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) : Prop :=
  (∀ t : ℕ, 1 ≤ t → t ≤ T + 1 →
    x t ∈ X ∩ D ∧
      ∀ z ∈ X ∩ D,
        η * (∑ s ∈ Finset.Ico 1 t, g s (x t)) + Φ (x t) ≤
          η * (∑ s ∈ Finset.Ico 1 t, g s z) + Φ z) ∧
  ∀ t : ℕ, 1 ≤ t → t ≤ T → IsSubgradientOnN X f (x t) (g t)

end ConvexOptAlg.MirrorDescent


