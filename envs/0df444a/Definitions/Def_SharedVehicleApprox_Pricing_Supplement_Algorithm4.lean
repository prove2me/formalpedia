-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm4
-- name    : SharedVehicleApprox_Pricing_Supplement_Algorithm4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:28:41.167027+00:00
-- url     : https://prove2.me/theorems/713a1de2-dd9f-48d2-b011-90f4018de893
-- title:
--   Algorithm 4 — the elevated flow relaxation with matching and its matching probabilities
-- statement:
--   Algorithm 4 chooses quantiles $q\in[0,1]^{n\times n}$ and matching rates $z\ge0$, with $z_{ij}=0$ for $(i,j)\notin E$, to solve
--
--   $$\begin{aligned}\max_{q,z}\ &\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})\\ \text{s.t.}\ &\sum_k(\varphi_{ki}q_{ki}+z_{ik})=\sum_j(\varphi_{ij}q_{ij}+z_{ji}),\qquad\sum_kz_{ki}\le\sum_j\varphi_{ji}q_{ji}\quad(\text{all }i),\end{aligned}$$
--
--   and outputs the matching probabilities $r_{ij}=z_{ij}/\sum_k\varphi_{ik}q_{ik}$. The definitions give feasibility, optimality and this output, which states Theorem 23.
--
--   **Formalization Note** The constraint $z\ge0$ is implicit on the page, as $z$ are rates. The balance and capacity constraints together give $\sum_kz_{ik}\le\sum_j\varphi_{ij}q_{ij}$, so $r$ has row sums at most one and is zero where the denominator vanishes.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 28 (PDF 29), Algorithm 4

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- Feasibility in the relaxation of Algorithm 4 (p. 28): quantiles in `[0, 1]`, matching rates
`z ≥ 0` (rates, left implicit on the page) supported on `E`,
`∑_k (φ_ki q_ki + z_ik) = ∑_j (φ_ij q_ij + z_ji)` and `∑_k z_ki ≤ ∑_j φ_ji q_ji`. -/
def IsAlg4Feasible {n : ℕ} (φ : Fin n → Fin n → ℝ) (E : Finset (Fin n × Fin n))
    (q z : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) ∧ (∀ i j, 0 ≤ z i j) ∧ (∀ i j, (i, j) ∉ E → z i j = 0) ∧
    (∀ i, ∑ k, (φ k i * q k i + z i k) = ∑ j, (φ i j * q i j + z j i)) ∧
    ∀ i, ∑ k, z k i ≤ ∑ j, φ j i * q j i

/-- `(q, z)` is an optimal solution of the relaxation of Algorithm 4: it maximizes
`∑_{i,j} φ_ij R_ij(q_ij)`. -/
def IsAlg4Optimal {n : ℕ} (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (E : Finset (Fin n × Fin n)) (q z : Fin n → Fin n → ℝ) : Prop :=
  IsAlg4Feasible φ E q z ∧
    ∀ q' z', IsAlg4Feasible φ E q' z' → elevObj φ I q' ≤ elevObj φ I q

/-- The matching probabilities `r_ij = z_ij / ∑_k φ_ik q_ik` output by Algorithm 4 (`0` when the
denominator is `0`). -/
noncomputable def matchProb {n : ℕ} (φ q z : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => z i j / ∑ k, φ i k * q i k

end SharedVehicleApprox.Pricing.Supplement


