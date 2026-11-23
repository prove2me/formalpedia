-- Prove2me | Definitions.Def_CtxInvOpt_Offline_Supplement_PolyCenter
-- name    : CtxInvOpt_Offline_Supplement_PolyCenter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:06:35.155414+00:00
-- url     : https://prove2.me/theorems/0b9d7938-042e-470b-88dc-af37fb32f0c9
-- title:
--   Algorithm 3, p. 26 — PolyCenter: axis and aperture of the polyhedral cone of the subspace update
-- statement:
--   This file formalizes **PolyCenter** (Algorithm 3), which ProjectedCones calls after a subspace update to restart its ellipsoidal cone.
--
--   The inputs are $p$ linearly independent unit vectors $\delta_1,\dots,\delta_p\in\mathbb R^d$ (the effective differences in $\tau(t+1)$) and a matrix $B$ with $p$ orthonormal rows spanning them. Set $\bar\delta_i=B\delta_i\in\mathbb R^p$, $\tilde z=\sum_i\bar\delta_i$ and $z=\tilde z/\|\tilde z\|$. For each $k$, $\chi_k$ is the unique solution of
--   $$c'z=1,\qquad \bar\delta_i'c=0\quad(i\neq k),$$
--   and $q_k=\chi_k/\|\chi_k\|$. Let $\hat c$ minimize $\|c\|^2$ over the convex hull of $q_1,\dots,q_p$. The outputs are
--   $$u=\frac{\hat c}{\|\hat c\|},\qquad \alpha=\arccos\Big(\frac{1}{\|\hat c\|}\min_k \hat c'q_k\Big).$$
--
--   The relation $\mathrm{IsPolyCenter}(\delta,B,u,\alpha)$ holds exactly when $(u,\alpha)$ is this output. The uniqueness of $\chi_k$ is part of the relation, and the minimum-norm point of a polytope is unique, so the output is determined by the input.
--
--   **Formalization Note** The page writes $q_k=\chi_k/\|\chi\|_2$ and mixes the indices $i$ and $k$ in the simplex constraint and in the minimum; these are read as $\|\chi_k\|$, $\sum_k\gamma_k=1$ and $\min_k$. Coordinate vectors use the Euclidean norm $\sqrt{v'v}$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 26, Algorithm 3 (PolyCenter)

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Supplement_ConeUpdateEta

namespace CtxInvOpt.Offline.Supplement

open Matrix

/-- **Algorithm 3 (PolyCenter), p. 26.** The relation "`(u, α)` is the output of
`PolyCenter({δ_k}, B, p)`" for the `p = m + 1` effective differences `δ_k ∈ ℝᵈ` of `τ(t+1)` and the
basis `B` (`p` orthonormal rows spanning them):

* `δ̄_k = Bδ_k`, `z̃ = Σ_k δ̄_k`, `z = z̃/‖z̃‖`;
* `χ_k` is the unique solution of `c′z = 1`, `δ̄_i′c = 0` (`i ≠ k`), and `q_k = χ_k/‖χ_k‖`;
* `ĉ` minimizes `‖c‖²` over the convex hull of `q_1, …, q_p`;
* `u = ĉ/‖ĉ‖` and `α = arccos((1/‖ĉ‖) min_k ĉ′q_k)`. -/
def IsPolyCenter {d m : ℕ} (δ : Fin (m + 1) → EuclideanSpace ℝ (Fin d))
    (B : Matrix (Fin (m + 1)) (Fin d) ℝ) (u : Fin (m + 1) → ℝ) (α : ℝ) : Prop :=
  let δbar : Fin (m + 1) → Fin (m + 1) → ℝ := fun i => B *ᵥ WithLp.ofLp (δ i)
  let zt : Fin (m + 1) → ℝ := ∑ i, δbar i
  let z : Fin (m + 1) → ℝ := (coordNorm zt)⁻¹ • zt
  ∃ χ : Fin (m + 1) → Fin (m + 1) → ℝ,
    (∀ k, χ k ⬝ᵥ z = 1 ∧ ∀ i, i ≠ k → δbar i ⬝ᵥ χ k = 0) ∧
    (∀ k (c : Fin (m + 1) → ℝ), (c ⬝ᵥ z = 1 ∧ ∀ i, i ≠ k → δbar i ⬝ᵥ c = 0) → c = χ k) ∧
    ∃ q : Fin (m + 1) → Fin (m + 1) → ℝ, (∀ k, q k = (coordNorm (χ k))⁻¹ • χ k) ∧
    ∃ chat : Fin (m + 1) → ℝ,
      chat ∈ convexHull ℝ (Set.range q) ∧
      (∀ c ∈ convexHull ℝ (Set.range q), chat ⬝ᵥ chat ≤ c ⬝ᵥ c) ∧
      u = (coordNorm chat)⁻¹ • chat ∧
      α = Real.arccos ((coordNorm chat)⁻¹ *
        Finset.univ.inf' Finset.univ_nonempty (fun k => chat ⬝ᵥ q k))

end CtxInvOpt.Offline.Supplement


