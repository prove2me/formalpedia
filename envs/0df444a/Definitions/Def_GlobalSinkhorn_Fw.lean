-- Prove2me | Definitions.Def_GlobalSinkhorn_Fw
-- name    : GlobalSinkhorn_Fw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:27.596735+00:00
-- url     : https://prove2.me/theorems/4bdb5c58-780c-4758-9aa8-759abcf79cab
-- title:
--   The map $\mathcal F(w)=[S^\top(Sw)^{-1}]^{-1}$
-- statement:
--   Let $S$ be a nonnegative doubly stochastic $n\times n$ matrix and $w\in\mathbb R^n_{>0}$. Define
--   $$
--   \mathcal F(w)=\big[S^\top (Sw)^{-1}\big]^{-1},\qquad \mathcal F(w)_j=\Big(\sum_i\frac{S_{ij}}{(Sw)_i}\Big)^{-1},
--   $$
--   with componentwise reciprocals. One full column–row normalization cycle sends $M(w)$ to $M(\mathcal F(w))$, so $\mathcal F$ is the Sinkhorn–Knopp dynamics written on column-scaling vectors.
--
--   **Formalization Note** Lean's total inverse is used for both reciprocals; for $w>0$ and doubly stochastic $S$ both inverted vectors are positive (milestone `GlobalSinkhorn.F_le_P`).
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Eq. (22), p.15

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- `F(w) = [Sᵀ (S w)⁻¹]⁻¹`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Eq. (22), p.15.

**Formalization Note.** Reciprocals are componentwise. For `w > 0` and doubly stochastic `S`
both inverted vectors are positive (`GlobalSinkhorn.F_le_P`), so Lean's total inverse never
fires. -/
noncomputable def Fw {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ((Sᵀ *ᵥ (fun i => ((S *ᵥ w) i)⁻¹)) j)⁻¹

end GlobalSinkhorn


