-- Prove2me | Definitions.Def_DCPenalty_Penalty_Problem
-- name    : DCPenalty_Penalty_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:55.224182+00:00
-- url     : https://prove2.me/theorems/ebd4bb3a-9398-48e2-904f-61e02a57ffd0
-- title:
--   (1.1)–(1.2), p. 2, and §1.1, pp. 5–6 — the constrained DC program, its standing assumptions, Ω, Ω_J, J_i(x), J(x), I_=(x), ℓ_f and the tangent cone
-- statement:
--   This file fixes the data of the **constrained DC program** of Lu, Sun and Zhou,
--
--   $$
--   \min_{x\in X}\ F(x)=\phi_0(x)+\zeta_0(x)-\psi_0(x)\quad\text{s.t.}\quad \phi_i(x)+\zeta_i(x)-\psi_i(x)\le 0,\quad i=1,\dots,I, \tag{1.1}
--   $$
--
--   where $\psi_i(x)=\max_{1\le j\le J_i}\psi_{i,j}(x)$ for $i=0,1,\dots,I$ (1.2), and the derived objects of §1.1.
--
--   **Standing assumptions** (p. 2). $X\subseteq\mathbb R^n$ is closed and convex; $\mathcal S\supseteq X$ is open (and convex); each $\zeta_i$ is convex and continuous on $\mathcal S$; each $\phi_i$ and each $\psi_{i,j}$ is convex and continuously differentiable on $\mathcal S$; and $\|\nabla\phi_i(x)-\nabla\phi_i(y)\|\le L_i\|x-y\|$ for all $x,y\in X$, with $L_i\ge 0$ and $L_0>0$.
--
--   **Derived objects.** With $\mathcal I=\{1,\dots,I\}$ and $\mathcal J=\{\mathbb J=(j_1,\dots,j_I): 1\le j_i\le J_i\}$:
--
--   1. the feasible region $\Omega=\{x\in X:\ \phi_i(x)+\zeta_i(x)-\psi_i(x)\le 0\ \forall i\in\mathcal I\}$;
--   2. for $\mathbb J\in\mathcal J$, $\Omega_{\mathbb J}=\{x\in X:\ \phi_i(x)+\zeta_i(x)-\psi_{i,j_i}(x)\le 0\ \forall i\in\mathcal I\}$ (1.14);
--   3. the active pieces $\mathcal J_i(x)=\{j:\ \psi_i(x)=\psi_{i,j}(x)\}$ and the active tuples $\mathcal J(x)=\{\mathbb J:\ j_i\in\mathcal J_i(x)\ \forall i\in\mathcal I\}$;
--   4. the active constraints $\mathcal I_=(x)=\{i\in\mathcal I:\ \phi_i(x)+\zeta_i(x)-\psi_i(x)=0\}$;
--   5. the linearization $\ell_f(x;\bar x)=f(\bar x)+\nabla f(\bar x)^T(x-\bar x)$ (1.19);
--   6. the (Bouligand) tangent cone of $Y$ at $x$,
--   $$
--   \mathcal T_Y(x)=\Big\{d:\ \exists\, x^k\in Y,\ x^k\to x,\ \tau_k\downarrow 0,\ d=\lim_{k\to\infty}\frac{x^k-x}{\tau_k}\Big\}.
--   $$
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`; gradients are Fréchet derivatives `fderiv`. Indices are `Fin (m+1)` with `m = I`: index `0` is the objective and constraint $i$ is `i.succ` for `i : Fin m`; a tuple $\mathbb J$ is a function `(i : Fin m) → Fin (J i.succ)`. Every piece set is nonempty (`J_pos`), so the maximum (1.2) is a `Finset.sup'`. Convexity of $\mathcal S$ is stated explicitly (the page says "convex on an open set $\mathcal S$", and `ConvexOn ℝ S` already contains it). The convention "$L_i=0$ if $\phi_i$ is affine" (p. 8) is not imposed. The tangent cone uses $\tau_k>0$, $\tau_k\to 0$ (monotonicity is immaterial after passing to a subsequence); Mathlib's `tangentConeAt`, which allows negative scalings, is not used. All functions are total; only their values on $X$ (or $\mathcal S$) matter.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 2, (1.1), (1.2) and the standing assumptions; pp. 5–6, §1.1, (1.14), J_i(x), J(x), I_=(x), T_Y(x), (1.19)

import Mathlib

namespace DCPenalty.Penalty

open Filter Topology

/-- Data of the constrained DC program (1.1)–(1.2) of Lu, Sun & Zhou (arXiv:2111.09263v1, p. 2).
Index `0 : Fin (m + 1)` is the objective and `i.succ` (for `i : Fin m`) is the constraint `i + 1`
of the paper's `{1, …, I}` (`m = I`). `J i` is the number of pieces of `ψ_i`, and `ψ i j` is the
piece `ψ_{i,j}`; `J_pos` says every piece set is nonempty. `L i` is the Lipschitz constant of
`∇φ_i` on `X`. -/
structure DCProblem (n m : ℕ) where
  X : Set (EuclideanSpace ℝ (Fin n))
  S : Set (EuclideanSpace ℝ (Fin n))
  J : Fin (m + 1) → ℕ
  J_pos : ∀ i, 0 < J i
  φ : Fin (m + 1) → EuclideanSpace ℝ (Fin n) → ℝ
  ζ : Fin (m + 1) → EuclideanSpace ℝ (Fin n) → ℝ
  ψ : (i : Fin (m + 1)) → Fin (J i) → EuclideanSpace ℝ (Fin n) → ℝ
  L : Fin (m + 1) → ℝ

namespace DCProblem

variable {n m : ℕ} (P : DCProblem n m)

/-- The standing assumptions of p. 2: `X` closed convex; `S` open (and convex, made explicit)
with `X ⊆ S`; every `ζ_i` convex and continuous on `S`; every `φ_i` and `ψ_{i,j}` convex and
continuously differentiable on `S`; `‖∇φ_i(x) − ∇φ_i(y)‖ ≤ L_i ‖x − y‖` on `X` with `L_i ≥ 0`;
and `L_0 > 0`. -/
structure Standing : Prop where
  isClosed_X : IsClosed P.X
  convex_X : Convex ℝ P.X
  isOpen_S : IsOpen P.S
  convex_S : Convex ℝ P.S
  X_subset_S : P.X ⊆ P.S
  ζ_convex : ∀ i, ConvexOn ℝ P.S (P.ζ i)
  ζ_cont : ∀ i, ContinuousOn (P.ζ i) P.S
  φ_convex : ∀ i, ConvexOn ℝ P.S (P.φ i)
  φ_C1 : ∀ i, ContDiffOn ℝ 1 (P.φ i) P.S
  ψ_convex : ∀ i j, ConvexOn ℝ P.S (P.ψ i j)
  ψ_C1 : ∀ i j, ContDiffOn ℝ 1 (P.ψ i j) P.S
  L_nonneg : ∀ i, 0 ≤ P.L i
  L0_pos : 0 < P.L 0
  φ_lipschitz : ∀ i, ∀ x ∈ P.X, ∀ y ∈ P.X,
    ‖fderiv ℝ (P.φ i) x - fderiv ℝ (P.φ i) y‖ ≤ P.L i * ‖x - y‖

/-- (1.2): `ψ_i(x) = max_{1 ≤ j ≤ J_i} ψ_{i,j}(x)`. -/
noncomputable def psi (i : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.sup' ⟨⟨0, P.J_pos i⟩, Finset.mem_univ _⟩ (fun j => P.ψ i j x)

/-- (1.1): the objective `F(x) = φ_0(x) + ζ_0(x) − ψ_0(x)`. -/
noncomputable def F (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.φ 0 x + P.ζ 0 x - P.psi 0 x

/-- The constraint function `φ_i(x) + ζ_i(x) − ψ_i(x)` of constraint `i + 1` (index `i.succ`). -/
noncomputable def g (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.φ i.succ x + P.ζ i.succ x - P.psi i.succ x

/-- §1.1, p. 5: the feasible region `Ω = {x ∈ X | φ_i(x) + ζ_i(x) − ψ_i(x) ≤ 0, ∀ i ∈ 𝓘}`. -/
def Ω : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ P.X ∧ ∀ i, P.g i x ≤ 0}

/-- (1.14): for a tuple `𝕁 = (j_1, …, j_I)`,
`Ω_𝕁 = {x ∈ X | φ_i(x) + ζ_i(x) − ψ_{i,j_i}(x) ≤ 0, ∀ i ∈ 𝓘}`. -/
def Ωj (jj : (i : Fin m) → Fin (P.J i.succ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ P.X ∧ ∀ i, P.φ i.succ x + P.ζ i.succ x - P.ψ i.succ (jj i) x ≤ 0}

/-- §1.1, p. 5: the active pieces `𝓙_i(x) = {j ∈ 𝓙_i | ψ_i(x) = ψ_{i,j}(x)}`. -/
def Jact (i : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin n)) : Set (Fin (P.J i)) :=
  {j | P.psi i x = P.ψ i j x}

/-- §1.1, p. 5: `𝓙(x) = {(j_1, …, j_I) | j_i ∈ 𝓙_i(x), ∀ i ∈ 𝓘}`. -/
def Jtup (x : EuclideanSpace ℝ (Fin n)) : Set ((i : Fin m) → Fin (P.J i.succ)) :=
  {jj | ∀ i, jj i ∈ P.Jact i.succ x}

/-- §1.1, p. 5: the active constraints `𝓘_=(x) = {i ∈ 𝓘 | φ_i(x) + ζ_i(x) − ψ_i(x) = 0}`. -/
def Ieq (x : EuclideanSpace ℝ (Fin n)) : Set (Fin m) :=
  {i | P.g i x = 0}

end DCProblem

/-- (1.19): the linearization `ℓ_f(x; x̄) = f(x̄) + ∇f(x̄)ᵀ(x − x̄)`. -/
noncomputable def lin {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f xbar + fderiv ℝ f xbar (x - xbar)

/-- §1.1, p. 5: the (Bouligand) tangent cone
`𝒯_Y(x) = {d | ∃ x^k ∈ Y, x^k → x, τ_k ↓ 0, d = lim (x^k − x)/τ_k}`, with `τ_k > 0`, `τ_k → 0`. -/
def tangentConeB {n : ℕ} (Y : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∃ xs : ℕ → EuclideanSpace ℝ (Fin n), ∃ τ : ℕ → ℝ, (∀ k, xs k ∈ Y) ∧
    Tendsto xs atTop (𝓝 x) ∧ (∀ k, 0 < τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
    Tendsto (fun k => (τ k)⁻¹ • (xs k - x)) atTop (𝓝 d)}

end DCPenalty.Penalty


