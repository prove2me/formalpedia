-- Prove2me | Definitions.Def_PathFindingLP_WeightFunction_SlackSensitivity
-- name    : PathFindingLP_WeightFunction_SlackSensitivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:39:24.151572+00:00
-- url     : https://prove2.me/theorems/1f60c683-561f-4a3f-ab22-8c9f2e049a48
-- title:
--   Projection matrix $P_{S^{-1}A}(w)$ and slack sensitivity $\gamma(s,w)$ (Definition 2)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ be the constraint matrix of a linear program $\min\{c^\top x : Ax\ge b\}$. For a slack vector $s\in\mathbb R^m_{>0}$ and a weight vector $w\in\mathbb R^m_{>0}$ write $S=\mathrm{diag}(s)$ and $W=\mathrm{diag}(w)$, and for a symmetric matrix $M$ let $\|v\|_M=\sqrt{v^\top M v}$.
--
--   The **projection matrix** is
--
--   $$
--   P_{S^{-1}A}(w) = W^{1/2}S^{-1}A\left(A^\top S^{-1}WS^{-1}A\right)^{-1}A^\top S^{-1}W^{1/2},
--   $$
--
--   the orthogonal projection onto the column space of $W^{1/2}S^{-1}A$ when $A$ has full column rank. The **slack sensitivity** of $(s,w)$ is
--
--   $$
--   \gamma(s,w) = \max_{i\in[m]} \left\|W^{-1/2}\mathbb 1_i\right\|_{P_{S^{-1}A}(w)},
--   $$
--
--   where $\mathbb 1_i$ is the $i$-th standard basis vector; equivalently $\gamma(s,w)=\max_i\sqrt{P_{ii}/w_i}$.
--
--   The slack sensitivity measures how much the Hessian of the weighted log-barrier can change under a small relative change of the slacks; it is one of the constants in the definition of a weight function.
--
--   **Formalization Note** `matNorm M v` is $\sqrt{v^\top M v}$ written literally, `projMatrix A s w` is the displayed product with $S^{-1}=\mathrm{diag}(1/s_i)$ and $W^{1/2}=\mathrm{diag}(\sqrt{w_i})$, and the inverse is Mathlib's `Matrix.inv` (which returns $0$ on singular matrices, so every theorem using these definitions assumes $\mathrm{rank}(A)=n$ and $s,w>0$). The maximum over $i\in[m]$ is a real supremum over the finite type `Fin m`; for $m\ge1$ it is the maximum.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 428, §IV.B, Definition 2 (slack sensitivity and projection matrix)

import Mathlib

namespace PathFindingLP.WeightFunction

open Matrix

/-- The weighted norm `‖v‖_M = √(vᵀ M v)` of a vector `v ∈ ℝ^m` with respect to an
`m × m` matrix `M` (Lee–Sidford 2014, §I notation). -/
noncomputable def matNorm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ (M *ᵥ v))

/-- The projection matrix of Definition 2 (Lee–Sidford 2014, §IV.B, p. 428):
`P_{S⁻¹A}(w) = W^{1/2} S⁻¹ A (Aᵀ S⁻¹ W S⁻¹ A)⁻¹ Aᵀ S⁻¹ W^{1/2}`,
where `S = diag(s)` and `W = diag(w)`. -/
noncomputable def projMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  diagonal (fun i => Real.sqrt (w i)) * diagonal (fun i => (s i)⁻¹) * A *
    (Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal w * diagonal (fun i => (s i)⁻¹) * A)⁻¹ *
    Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal (fun i => Real.sqrt (w i))

/-- The slack sensitivity of Definition 2 (Lee–Sidford 2014, §IV.B, p. 428):
`γ(s, w) = max_{i ∈ [m]} ‖W^{-1/2} 𝟙_i‖_{P_{S⁻¹A}(w)}`. -/
noncomputable def slackSensitivity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) :
    ℝ :=
  ⨆ i : Fin m,
    matNorm (projMatrix A s w) (diagonal (fun j => (Real.sqrt (w j))⁻¹) *ᵥ Pi.single i 1)

end PathFindingLP.WeightFunction


