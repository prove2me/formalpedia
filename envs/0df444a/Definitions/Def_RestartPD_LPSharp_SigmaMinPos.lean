-- Prove2me | Definitions.Def_RestartPD_LPSharp_SigmaMinPos
-- name    : RestartPD_LPSharp_SigmaMinPos
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:23.401115+00:00
-- url     : https://prove2.me/theorems/5a280e28-63b7-433b-abb1-b853d3b2b856
-- title:
--   Notation, p. 4 — σ⁺_min(H), the minimum nonzero singular value of a matrix
-- statement:
--   For a matrix $H\in\mathbb R^{m\times n}$, the **minimum nonzero singular value** is
--   $$\sigma^+_{\min}(H)=\min\{\sigma>0:\ \sigma^2 \text{ is an eigenvalue of } H^\top H\}.$$
--   It governs how far a point can be from the solution set of $Hz=h$ relative to its residual (Lemma 2 of the paper).
--
--   **Formalization Note** It is the infimum of the set of $\sigma>0$ for which some nonzero $v$ satisfies $H^\top H v=\sigma^2 v$. The set is finite, so the infimum is a minimum when $H\ne0$; for $H=0$ the set is empty and Lean's value is $0$ (the paper leaves $\sigma^+_{\min}(0)$ undefined).
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 4, Notation (σ⁺_min)

import Mathlib

namespace RestartPD.LPSharp

open scoped Matrix

/-- `σ⁺_min(H)`, the minimum nonzero singular value of `H ∈ ℝ^{m×n}` (Notation, p. 4): the least
`σ > 0` such that `σ²` is an eigenvalue of `HᵀH`. For `H = 0` there is no such `σ` and the value is
`sInf ∅ = 0`. -/
noncomputable def sigmaMinPos {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {σ : ℝ | 0 < σ ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ (Hᵀ * H).mulVec v = σ ^ 2 • v}

end RestartPD.LPSharp


