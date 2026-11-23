-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm2
-- name    : SharedVehicleApprox_Pricing_Supplement_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:30:15.470248+00:00
-- url     : https://prove2.me/theorems/ae0ec638-372f-439f-b283-bdfc2afa14fc
-- title:
--   Algorithm 2 — the rate-limited elevated flow relaxation and its scaled output
-- statement:
--   Algorithm 2 first finds an optimum $q'$ of
--
--   $$\max_q\ \sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})\quad\text{s.t.}\quad\sum_k\varphi_{ki}q_{ki}=\sum_j\varphi_{ij}q_{ij}\ \ \forall i,\qquad\sum_{i,j}\varphi_{ij}\tau_{ij}q_{ij}\le m,\qquad q_{ij}\in[0,1].$$
--
--   It then outputs, for the scaling parameter $\varepsilon$,
--
--   $$\tilde q=\begin{cases}(1-\varepsilon)q'&\text{if }\sum_{i,j}\varphi_{ij}\tau_{ij}q'_{ij}\ge m(1-\varepsilon),\\ q'&\text{otherwise.}\end{cases}$$
--
--   The definitions give feasibility, optimality of step 1 and the output of step 2, which state Theorem 18.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 22 (PDF 23), Algorithm 2

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- Feasibility in the rate-limited relaxation of Algorithm 2 (p. 22): balanced quantiles in
`[0, 1]` with `∑_{i,j} φ_ij τ_ij q_ij ≤ m`. -/
def IsAlg2Feasible {n : ℕ} (φ τ : Fin n → Fin n → ℝ) (m : ℕ) (q : Fin n → Fin n → ℝ) : Prop :=
  IsRelaxFeasible φ q ∧ ∑ i, ∑ j, φ i j * τ i j * q i j ≤ m

/-- `q'` solves step 1 of Algorithm 2: it maximizes `∑_{i,j} φ_ij R_ij(q_ij)` over the
rate-limited relaxation. -/
def IsAlg2Optimal {n : ℕ} (φ τ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ) (m : ℕ)
    (q' : Fin n → Fin n → ℝ) : Prop :=
  IsAlg2Feasible φ τ m q' ∧
    ∀ q, IsAlg2Feasible φ τ m q → elevObj φ I q ≤ elevObj φ I q'

/-- The output of step 2 of Algorithm 2: `(1 − ε) q'` if `∑_{i,j} φ_ij τ_ij q'_ij ≥ m (1 − ε)`,
and `q'` otherwise. -/
noncomputable def alg2Output {n : ℕ} (φ τ : Fin n → Fin n → ℝ) (m : ℕ) (ε : ℝ)
    (q' : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  if (m : ℝ) * (1 - ε) ≤ ∑ i, ∑ j, φ i j * τ i j * q' i j then fun i j => q' i j * (1 - ε)
  else q'

end SharedVehicleApprox.Pricing.Supplement


