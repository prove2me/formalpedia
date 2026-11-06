-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
-- name    : QEC_Semantics_Dynamics_Davies_NormBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:01:45.490729+00:00
-- url     : https://prove2.me/theorems/e8ff0f57-1d1e-409b-a16e-a979c24a1cce
-- title:
--   Norm Bound
-- statement:
--   Definitions and structural lemmas for Norm Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/NormBound.lean

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators ComplexOrder
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def rateSquareSum (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (rate : Frequency e → ℝ) : Operator V :=
  ∑ w : Frequency e, (rate w : ℂ) •
    (LinearMap.adjoint (frequencyComponent b e A w.val) * frequencyComponent b e A w.val)
end
end QEC.Semantics.Davies


