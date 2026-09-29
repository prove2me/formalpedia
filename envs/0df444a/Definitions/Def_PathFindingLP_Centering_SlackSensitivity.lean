-- Prove2me | Definitions.Def_PathFindingLP_Centering_SlackSensitivity
-- name    : PathFindingLP_Centering_SlackSensitivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:35:34.578301+00:00
-- url     : https://prove2.me/theorems/531c385a-6de9-48ca-978a-6cee8f65e8ed
-- title:
--   Definition 2: projection matrix $P_{S^{-1}A}(\vec w)$ and slack sensitivity $\gamma(\vec s,\vec w)$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ and let $s,w\in\mathbb R^m_{>0}$. Write $S=\mathrm{diag}(s)$, $W=\mathrm{diag}(w)$, $W^{1/2}=\mathrm{diag}(\sqrt{w_i})$, $W^{-1/2}=\mathrm{diag}(1/\sqrt{w_i})$, and let $\vec 1_i$ be the $i$-th standard basis vector of $\mathbb R^m$. The **projection matrix** is
--   $$P_{S^{-1}A}(w)=W^{1/2}S^{-1}A\big(A^TS^{-1}WS^{-1}A\big)^{-1}A^TS^{-1}W^{1/2},$$
--   the orthogonal projection onto the column space of $W^{1/2}S^{-1}A$. The **slack sensitivity** is
--   $$\gamma(s,w)=\max_{i\in[m]}\big\|W^{-1/2}\vec 1_i\big\|_{P_{S^{-1}A}(w)},\qquad \|v\|_M=\sqrt{v^TMv}.$$
--   Equivalently $\gamma(s,w)=\max_i\sqrt{P_{ii}/w_i}$.
--
--   The slack sensitivity bounds how much a Newton step can change the slacks relative to their size, and hence how much the Hessian of the weighted barrier changes along a step. It governs the region of quadratic convergence of the weighted Newton step (Lemma 3) and is one of the constants a weight function must control.
--
--   **Formalization Note** The norm is written literally, $\sqrt{u^TPu}$ with $u=W^{-1/2}\vec 1_i$. The maximum over $[m]$ is a supremum over `Fin m`; for $m\ge1$ it is attained, and for $m=0$ it is $0$. $S^{-1}$ is the diagonal matrix of reciprocals, and the matrix inverse is Mathlib's `Matrix.inv` (zero on singular matrices); theorems using $\gamma$ assume $A$ has full column rank, so the inverse is genuine for positive $s,w$.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433, p. 428, §IV.B, Definition 2 (slack sensitivity and the projection matrix P_{S_x^{-1}A}(w))

import Mathlib
import Definitions.Def_PathFindingLP_Centering_WeightedCentralPath

open Matrix

namespace PathFindingLP.Centering

variable {m n : ℕ}

/-- The projection matrix of Definition 2 (§IV.B, p. 428):
`P_{S⁻¹A}(w) = W^{1/2} S⁻¹ A (Aᵀ S⁻¹ W S⁻¹ A)⁻¹ Aᵀ S⁻¹ W^{1/2}`, with `S = diag(s)`,
`W = diag(w)`, `W^{1/2} = diag(√wᵢ)` and `S⁻¹ = diag(1 / sᵢ)`. -/
noncomputable def projectionMatrix (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  diagonal (fun i => Real.sqrt (w i)) * diagonal (fun i => (s i)⁻¹) * A *
    (weightedGram A s w)⁻¹ * Aᵀ * diagonal (fun i => (s i)⁻¹) *
    diagonal (fun i => Real.sqrt (w i))

/-- The slack sensitivity of Definition 2 (§IV.B, p. 428):
`γ(s, w) = max_{i ∈ [m]} ‖W^{-1/2} 𝟙ᵢ‖_{P_{S⁻¹A}(w)}`, where `𝟙ᵢ` is the `i`-th standard basis
vector and `W^{-1/2} = diag(1 / √wᵢ)`. The maximum over the finite index set is written as a
supremum over `Fin m`. -/
noncomputable def slackSensitivity (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) : ℝ :=
  ⨆ i : Fin m,
    matNorm (projectionMatrix A s w)
      (diagonal (fun j => (Real.sqrt (w j))⁻¹) *ᵥ Pi.single i (1 : ℝ))

end PathFindingLP.Centering


