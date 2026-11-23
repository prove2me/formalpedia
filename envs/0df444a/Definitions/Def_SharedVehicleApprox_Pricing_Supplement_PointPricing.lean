-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing
-- name    : SharedVehicleApprox_Pricing_Supplement_PointPricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:29:25.656079+00:00
-- url     : https://prove2.me/theorems/7f818a78-3207-4381-a756-84c1990b6368
-- title:
--   App. C — point pricing and Algorithm 6, the elevated flow relaxation over point quantiles
-- statement:
--   Under **point pricing** the quantile depends only on the origin: $q_{ij}=q_i$ for a state-independent policy and $q_{ij}(x)=q_i(x)$ for a state-dependent one. Algorithm 6 solves
--
--   $$\max_q\ \sum_{i,j}\varphi_{ij}R_{ij}(q_i)\quad\text{s.t.}\quad\sum_k\varphi_{ki}q_k=\sum_j\varphi_{ij}q_i,\qquad q_i\in[0,1]\quad(\text{all }i).$$
--
--   The definitions embed point quantiles and point policies among the matrix-valued ones and define an optimum of Algorithm 6. They state Theorem 28 and Lemma 33.
--
--   **Formalization Note** The reward curve $R_{ij}$ may depend on the destination even though the quantile does not.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 36 (PDF 37), App. C, Algorithm 6

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- A vector of point quantiles as a quantile matrix: `q_ij = q_i` (App. C, p. 36). -/
def pointQuantile {n : ℕ} (q : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i _ => q i

/-- A state-dependent point policy as a pricing policy: `q_ij(x) = q_i(x)`. -/
def pointPolicy {n : ℕ} (q : (Fin n → ℕ) → Fin n → ℝ) : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
  fun x i _ => q x i

/-- `q` is an optimal solution of the relaxation of Algorithm 6 (p. 36): it maximizes
`∑_{i,j} φ_ij R_ij(q_i)` subject to `q_i ∈ [0, 1]` and `∑_k φ_ki q_k = ∑_j φ_ij q_i`. -/
def IsAlg6Optimal {n : ℕ} (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : Fin n → ℝ) : Prop :=
  IsRelaxFeasible φ (pointQuantile q) ∧
    ∀ q', IsRelaxFeasible φ (pointQuantile q') →
      elevObj φ I (pointQuantile q') ≤ elevObj φ I (pointQuantile q)

end SharedVehicleApprox.Pricing.Supplement


