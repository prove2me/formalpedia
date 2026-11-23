-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_MultiObjective
-- name    : SharedVehicleApprox_Pricing_Supplement_MultiObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:29:02.714414+00:00
-- url     : https://prove2.me/theorems/d41b31c8-ff83-4ae0-b3cd-8c855a43f8ae
-- title:
--   §5.3 — Algorithm 5, the elevated flow relaxation with a second-objective constraint
-- statement:
--   Two families of per-ride rewards define objectives $\Phi$ and $\Psi$ on the same system, and $c$ is a requirement on $\Psi$. Algorithm 5 solves
--
--   $$\max_q\ \hat\Phi(q)=\sum_{i,j}\varphi_{ij}R^\Phi_{ij}(q_{ij})\quad\text{s.t.}\quad q\in[0,1]^{n\times n},\ \ \sum_k\varphi_{ki}q_{ki}=\sum_j\varphi_{ij}q_{ij}\ \ \forall i,\ \ \hat\Psi(q)=\sum_{i,j}\varphi_{ij}R^\Psi_{ij}(q_{ij})\ge c.$$
--
--   The definitions give feasibility and optimality, which state Theorem 24. Feasibility is that of Algorithm 1 with the one additional constraint.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, pp. 28–29 (PDF 29–30), §5.3, Algorithm 5

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- Feasibility in the relaxation of Algorithm 5 (p. 29): balanced quantiles in `[0, 1]` with
elevated second objective `Ψ̂(q) ≥ c`. -/
def IsAlg5Feasible {n : ℕ} (φ : Fin n → Fin n → ℝ) (IΨ : Fin n → Fin n → ℝ → ℝ) (c : ℝ)
    (q : Fin n → Fin n → ℝ) : Prop :=
  IsRelaxFeasible φ q ∧ c ≤ elevObj φ IΨ q

/-- `q` is an optimal solution of the relaxation of Algorithm 5: it maximizes `Φ̂`. -/
def IsAlg5Optimal {n : ℕ} (φ : Fin n → Fin n → ℝ) (IΦ IΨ : Fin n → Fin n → ℝ → ℝ) (c : ℝ)
    (q : Fin n → Fin n → ℝ) : Prop :=
  IsAlg5Feasible φ IΨ c q ∧
    ∀ q', IsAlg5Feasible φ IΨ c q' → elevObj φ IΦ q' ≤ elevObj φ IΦ q

end SharedVehicleApprox.Pricing.Supplement


