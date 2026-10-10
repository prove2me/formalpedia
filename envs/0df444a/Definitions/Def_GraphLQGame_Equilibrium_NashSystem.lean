-- Prove2me | Definitions.Def_GraphLQGame_Equilibrium_NashSystem
-- name    : GraphLQGame_Equilibrium_NashSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:27:14.25007+00:00
-- url     : https://prove2.me/theorems/2ac063df-d8e8-4469-86a6-605c6ccc0db8
-- title:
--   The Nash system (4.1), the quadratic ansatz (4.5), the Riccati residual (4.6), and the candidate solution $F^i$ (4.13), $h_i$ (4.9)
-- statement:
--   Let $G$ be a graph on $n$ vertices with Laplacian $L=L_G$, and $c,\sigma,T>0$. Write $\partial_k$, $\partial_{kk}$ for partial derivatives in $x_k$ and $e_k$ for the standard basis.
--
--   1. $(v_1,\dots,v_n)$, $v_i:[0,T]\times\mathbb R^n\to\mathbb R$, is a **classical solution of the Nash system** (4.1) if each $v_i$ is differentiable in $t$ and $C^2$ in $x$ for $t\in(0,T)$, and
--   $$0=\partial_tv_i-\tfrac12(\partial_iv_i)^2-\sum_{k\ne i}\partial_kv_k\,\partial_kv_i+\frac{\sigma^2}{2}\sum_{k=1}^n\partial_{kk}v_i,\qquad v_i(T,x)=\tfrac12c\,(e_i^\top Lx)^2 .$$
--   2. The ansatz (4.5): $v_i(t,x)=\tfrac12x^\top F^i(t)x+h_i(t)$.
--   3. The Riccati residual of (4.6): $\dot F^i-\sum_jF^je_je_j^\top F^i-F^i\sum_je_je_j^\top F^j+F^ie_ie_i^\top F^i$.
--   4. The candidate (4.13): $F^i(t)=\big(\mathrm{Tr}(P_G(t))/n\big)^{-1}P_G(t)e_ie_i^\top P_G(t)$, and (4.9): $h_i(t)=\frac{\sigma^2}{2}\int_t^T\mathrm{Tr}(F^i(s))\,ds$.
--
--   These encode the reduction of the game to a Riccati system and its explicit solution in §4.
--
--   **Formalization Note** Partial derivatives are Fréchet derivatives along basis vectors; $\dot F$ is the entrywise derivative; $e_je_j^\top$ is `Matrix.single j j 1`. Vertices are `Fin n`.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §4.2–4.4, pp. 24–26, (4.1), (4.5), (4.6), (4.9), (4.13)

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium

namespace GraphLQGame.Equilibrium

/-- The partial derivative `∂_k g(x)` of `g : ℝⁿ → ℝ` in the direction of the `k`-th basis vector. -/
noncomputable def pd {n : ℕ} (g : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single k 1)

/-- The second partial derivative `∂_{kk} g(x)`. -/
noncomputable def pdd {n : ℕ} (g : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ g y (Pi.single k 1)) x (Pi.single k 1)

/-- `(v_1, …, v_n)` is a classical solution of the Nash system (4.1) (§4.2, p. 24):
for `t ∈ (0, T)` each `v_i(·, x)` is differentiable in `t` and each `v_i(t, ·)` is `C²`, and
`0 = ∂_t v_i − ½ (∂_i v_i)² − Σ_{k ≠ i} ∂_k v_k ∂_k v_i + (σ²/2) Σ_k ∂_{kk} v_i`,
with terminal condition `v_i(T, x) = ½ c (e_iᵀ L_G x)²`. -/
def IsNashSystemSol {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c σ T : ℝ)
    (v : Fin n → ℝ → (Fin n → ℝ) → ℝ) : Prop :=
  (∀ i, ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x, DifferentiableAt ℝ (fun s => v i s x) t) ∧
  (∀ i, ∀ t ∈ Set.Ioo (0 : ℝ) T, ContDiff ℝ 2 (v i t)) ∧
  (∀ i, ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x,
    0 = deriv (fun s => v i s x) t - 1 / 2 * (pd (v i t) i x) ^ 2
      - ∑ k ∈ Finset.univ.erase i, pd (v k t) k x * pd (v i t) k x
      + σ ^ 2 / 2 * ∑ k, pdd (v i t) k x) ∧
  (∀ i x, v i T x = 1 / 2 * c * ((lap G).mulVec x i) ^ 2)

/-- The quadratic ansatz (4.5), `v_i(t, x) = ½ xᵀ F^i(t) x + h_i(t)` (§4.3, p. 24). -/
noncomputable def ansatz {n : ℕ} (F : Fin n → ℝ → Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ → ℝ)
    (i : Fin n) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 / 2 * (x ⬝ᵥ (F i t).mulVec x) + h i t

/-- The entrywise time derivative `Ḟ(t)` of a matrix-valued function. -/
noncomputable def mderiv {n : ℕ} (F : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k => deriv (fun s => F s j k) t

/-- The right side of the Riccati system (4.6) (Lemma 4.2, p. 25):
`Ḟ^i − Σ_j F^j e_j e_jᵀ F^i − F^i Σ_j e_j e_jᵀ F^j + F^i e_i e_iᵀ F^i` (here `e_j e_jᵀ` is
`Matrix.single j j 1`). -/
noncomputable def riccatiRes {n : ℕ} (F : Fin n → ℝ → Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  mderiv (F i) t - (∑ j, F j t * Matrix.single j j 1) * F i t
    - F i t * (∑ j, Matrix.single j j 1 * F j t) + F i t * Matrix.single i i 1 * F i t

/-- The candidate solution (4.13) (§4.4, p. 26):
`F^i(t) = (Tr(P_G(t))/n)⁻¹ P_G(t) e_i e_iᵀ P_G(t)`. -/
noncomputable def Fmat {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c T : ℝ)
    (f : ℝ → ℝ) (i : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((PG G c T f t).trace / n)⁻¹ • (PG G c T f t * Matrix.single i i 1 * PG G c T f t)

/-- The scalar part (4.9) (p. 25): `h_i(t) = (σ²/2) ∫_t^T Tr(F^i(s)) ds`, with `F^i` from (4.13). -/
noncomputable def hfun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c σ T : ℝ)
    (f : ℝ → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  σ ^ 2 / 2 * ∫ s in t..T, (Fmat G c T f i s).trace

end GraphLQGame.Equilibrium


