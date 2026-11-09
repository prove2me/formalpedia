-- Prove2me | Definitions.Def_AutobidSPPE_spendJac
-- name    : AutobidSPPE_spendJac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:24.219723+00:00
-- url     : https://prove2.me/theorems/3d6d6afa-6a3b-42b9-936b-2ada06acb48b
-- title:
--   Endpoint spending Jacobian $J_s=D_y\mathsf s$
-- statement:
--   The **endpoint spending Jacobian** at an endpoint profile $y$ is the $n\times n$ matrix
--   $$
--   (J_s)_{ij} = \frac{\partial \mathsf s_i}{\partial y_j}(y)
--   $$
--   of the map $y\mapsto(\mathsf s_1(y),\dots,\mathsf s_n(y))$.
--
--   **Formalization Note** The Fréchet derivative of the spending map, converted to a matrix; it is the zero matrix where the map is not differentiable. Lemma 2.9 shows differentiability on the positive orthant, the only place it is used.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.9, p.15; Table 1, p.9

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend

namespace AutobidSPPE

/-- The endpoint spending Jacobian `J_s = D_y𝗌` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Lemma 2.9, p.15; Table 1, p.9): the
matrix with entries `(J_s)ᵢⱼ = ∂𝗌ᵢ/∂yⱼ` of the map `y ↦ (𝗌ᵢ(y))ᵢ`.

**Formalization Note** The Fréchet derivative turned into a matrix with `LinearMap.toMatrix'`;
it is `0` where the map is not differentiable (Lemma 2.9 proves differentiability on the positive
orthant, where it is used). -/
noncomputable def spendJac {n : ℕ} (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix'
    ((fderiv ℝ (fun z : Fin n → ℝ => fun i => endpointSpend z i) y :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))

end AutobidSPPE


