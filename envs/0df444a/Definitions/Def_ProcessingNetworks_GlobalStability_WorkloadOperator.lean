-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_WorkloadOperator
-- name    : ProcessingNetworks_GlobalStability_WorkloadOperator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:09:29.714463+00:00
-- url     : https://prove2.me/theorems/507eeb8f-257b-4a4a-ac44-2ab015642a24
-- title:
--   The workload operator and total arrival rates, restated
-- statement:
--   Restated from mission VI (see that mission's `MODERATION_NOTES.md`): the workload operator
--   $W(z) := AM(I-P')^{-1}z$ (Eq. 8.24), the total arrival rate vector $\alpha := (I-P')^{-1}\lambda$
--   (Eq. 2.38), and `IsRoutingInverse`, asserting a supplied matrix `Q` genuinely represents
--   $(I-P')^{-1}$. Used here for the standard load condition $\rho = W(\lambda) < b$ in Theorem
--   8.24, and for `totalArrivalRates` in Lemma 8.20.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 145, Eqs. (8.24)-(8.25), (2.36)-(2.38) (restated)

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

open Matrix

/-- The workload operator `W : ℝ^I_+ → ℝ^K_+`, Eq. (8.24), restated from mission VI's
`workloadOperator`: `W(z) := AM(I-P')⁻¹z`. `Q` stands for `(I-P')⁻¹`, supplied as data with its
defining two-sided-inverse property. -/
def workloadOperator {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (z : Fin I → ℝ) (k : Fin K) : ℝ :=
  ∑ i ∈ poolBuffers dat k, dat.m i * (Q.mulVec z) i

/-- `α`, the vector of total arrival rates (Eq. 2.38), the unique solution of the traffic
equations `α = λ + P'α` (Eq. 2.36), i.e. `α := Qλ`. -/
def totalArrivalRates {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ) :
    Fin I → ℝ :=
  Q.mulVec dat.lam

/-- `Q` genuinely represents the routing-matrix inverse `(I - P')⁻¹`. -/
def IsRoutingInverse {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (Q : Matrix (Fin I) (Fin I) ℝ) : Prop :=
  Q * (1 - Pᵀ) = 1 ∧ (1 - Pᵀ) * Q = 1

end ProcessingNetworks.GlobalStability


