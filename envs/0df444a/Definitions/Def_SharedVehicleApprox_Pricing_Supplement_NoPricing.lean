-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing
-- name    : SharedVehicleApprox_Pricing_Supplement_NoPricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:27:26.259797+00:00
-- url     : https://prove2.me/theorems/e86b606b-46f6-4024-a9dd-d3464ea3477a
-- title:
--   App. D.1 — redirection without prices: Algorithm 8, its output and the infinite-unit objective
-- statement:
--   **Without prices** the per-ride rewards $I_{ij}$ are constants and every customer is served whenever a unit is present at the origin. Algorithm 8 chooses $q\in[0,1]^n$, read as the served fractions, and $z\ge0$ to solve
--
--   $$\begin{aligned}\max_{q,z}\ &\sum_{i,j}\bigl(\varphi_{ij}q_iI_{ij}-c_{ij}z_{ij}\bigr)\\ \text{s.t.}\ &\sum_k(\varphi_{ki}q_k+z_{ki})=\sum_j(\varphi_{ij}q_i+z_{ij}),\qquad\sum_kz_{ik}\le\sum_j\varphi_{ji}q_j\quad(\text{all }i),\end{aligned}$$
--
--   and outputs $r_{ij}=z_{ij}/\sum_k\varphi_{ki}q_k$ (zero when the denominator is zero). For traffic intensities $\rho$ the **infinite-unit objective** of a redirection matrix $r$ is
--
--   $$\mathrm{Obj}_\infty(r)=\sum_i\frac{\rho_i}{\rho_{\max}}B_i,\qquad B_i=\sum_j\varphi_{ij}\Bigl(I_{ij}-\sum_kr_{jk}c_{jk}\Bigr),$$
--
--   where $B_i$ charges node $i$ for the redirections of its trips.
--
--   These objects state Lemma 30 and Theorems 31 and 34.
--
--   **Formalization Note** Feasibility is that of Algorithm 3 at $q_{ij}=q_i$. The implemented policy has every quantile equal to one; the solution $q$ only defines $r$.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, pp. 38–39 (PDF 39–40), App. D.1, Algorithm 8; p. 27 (PDF 28), proof of Theorem 22

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- Constant per-ride rewards `I i j` (App. D.1, p. 38), as functions of the quantile. -/
def constReward {n : ℕ} (I : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ → ℝ :=
  fun i j _ => I i j

/-- Without prices every customer is served whenever a unit is present at the origin. -/
def serveAll {n : ℕ} : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
  toPolicy (fun _ _ => 1)

/-- Feasibility in the relaxation of Algorithm 8 (p. 39): `q_i ∈ [0, 1]`, `z ≥ 0`, and the
constraints of Algorithm 3 with `q_ij` replaced by `q_i`. -/
def IsAlg8Feasible {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : Fin n → ℝ) (z : Fin n → Fin n → ℝ) :
    Prop :=
  IsAlg3Feasible φ (fun i _ => q i) z

/-- The objective `∑_{i,j} (φ_ij q_i I_ij − c_ij z_ij)` of Algorithm 8, the elevated objective
without prices. -/
def alg8Obj {n : ℕ} (φ I c : Fin n → Fin n → ℝ) (q : Fin n → ℝ) (z : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (φ i j * q i * I i j - c i j * z i j)

/-- `(q, z)` is an optimal solution of the relaxation of Algorithm 8. -/
def IsAlg8Optimal {n : ℕ} (φ I c : Fin n → Fin n → ℝ) (q : Fin n → ℝ)
    (z : Fin n → Fin n → ℝ) : Prop :=
  IsAlg8Feasible φ q z ∧
    ∀ q' z', IsAlg8Feasible φ q' z' → alg8Obj φ I c q' z' ≤ alg8Obj φ I c q z

/-- The output `r_ij = z_ij / ∑_k φ_ki q_k` of Algorithms 8 and 9 (`0` when the denominator is
`0`). -/
noncomputable def noPriceRedirectProb {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : Fin n → ℝ)
    (z : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  redirectProb φ (fun i _ => q i) z

/-- The infinite-unit objective of a redirection policy `r` without prices, with traffic
intensities `ρ`: `∑_i A_i,∞ B_i`, where `A_i,∞ = ρ_i / ρ_max` and
`B_i = ∑_j φ_ij (I_ij − ∑_k r_jk c_jk)` charges node `i` for the redirections of its trips
(proof of Theorem 22, p. 27, with every quantile equal to one). -/
noncomputable def noPriceObjInf {n : ℕ} [NeZero n] (φ I c r : Fin n → Fin n → ℝ)
    (ρ : Fin n → ℝ) : ℝ :=
  ∑ i, availInf ρ i * ∑ j, φ i j * (I i j - ∑ k, r j k * c j k)

end SharedVehicleApprox.Pricing.Supplement


