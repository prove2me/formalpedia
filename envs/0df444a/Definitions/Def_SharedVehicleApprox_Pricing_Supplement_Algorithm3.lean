-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
-- name    : SharedVehicleApprox_Pricing_Supplement_Algorithm3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:26:37.824332+00:00
-- url     : https://prove2.me/theorems/fa6555a2-1362-42d6-b778-85bafbca819f
-- title:
--   Algorithm 3 — the elevated flow relaxation with supply redirection and its redirection probabilities
-- statement:
--   Algorithm 3 chooses quantiles $q\in[0,1]^{n\times n}$ and redirection rates $z\ge0$ to solve
--
--   $$\begin{aligned}\max_{q,z}\ &\sum_{i,j}\bigl(\varphi_{ij}R_{ij}(q_{ij})-c_{ij}z_{ij}\bigr)\\ \text{s.t.}\ &\sum_k(\varphi_{ki}q_{ki}+z_{ki})=\sum_j(\varphi_{ij}q_{ij}+z_{ij}),\qquad\sum_kz_{ik}\le\sum_j\varphi_{ji}q_{ji}\quad(\text{all }i).\end{aligned}$$
--
--   The definitions give feasibility, the objective, optimality and the output
--
--   $$r_{ij}=\frac{z_{ij}}{\sum_k\varphi_{ki}q_{ki}},$$
--
--   the redirected rate over the rate of non-empty units arriving at $i$.
--
--   **Formalization Note** Page 25 prints the output with denominator $\sum_k\varphi_{ki}$. This is a misprint: the sentence before the algorithm and the proof of Lemma 21 use $\sum_k\varphi_{ki}q_{ki}$. The constraint $z\ge0$ is implicit on the page, as $z$ are rates. When the denominator is zero, feasibility forces $z_{ij}=0$ and the output is zero.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 25 (PDF 26), Algorithm 3, with the proof of Lemma 21, p. 26 (PDF 27)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- Feasibility in the relaxation of Algorithm 3 (p. 25): quantiles in `[0, 1]`, redirection rates
`z ≥ 0` (rates, left implicit on the page), supply circulation
`∑_k (φ_ki q_ki + z_ki) = ∑_j (φ_ij q_ij + z_ij)` and `∑_k z_ik ≤ ∑_j φ_ji q_ji`. -/
def IsAlg3Feasible {n : ℕ} (φ q z : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) ∧ (∀ i j, 0 ≤ z i j) ∧
    (∀ i, ∑ k, (φ k i * q k i + z k i) = ∑ j, (φ i j * q i j + z i j)) ∧
    ∀ i, ∑ k, z i k ≤ ∑ j, φ j i * q j i

/-- The objective `∑_{i,j} (φ_ij R_ij(q_ij) − c_ij z_ij)` of Algorithm 3. -/
def alg3Obj {n : ℕ} (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (c q z : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (φ i j * rewardCurve I i j (q i j) - c i j * z i j)

/-- `(q, z)` is an optimal solution of the relaxation of Algorithm 3. -/
def IsAlg3Optimal {n : ℕ} (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (c q z : Fin n → Fin n → ℝ) : Prop :=
  IsAlg3Feasible φ q z ∧
    ∀ q' z', IsAlg3Feasible φ q' z' → alg3Obj φ I c q' z' ≤ alg3Obj φ I c q z

/-- The redirection probabilities `r_ij = z_ij / ∑_k φ_ki q_ki`: the rate of redirected units over
the total rate of non-empty units arriving at `i` (p. 25 and the proof of Lemma 21, p. 26). The
printed output line of Algorithm 3 omits the factor `q_ki` by a misprint. The value is `0` when
the denominator is `0`. -/
noncomputable def redirectProb {n : ℕ} (φ q z : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => z i j / ∑ k, φ k i * q k i

end SharedVehicleApprox.Pricing.Supplement


