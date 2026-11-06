-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
-- name    : QEC_Semantics_Dynamics_LieTrotter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:35:44.364812+00:00
-- url     : https://prove2.me/theorems/2030f502-93d8-4410-92fd-13b48e2fb49a
-- title:
--   Lie Trotter
-- statement:
--   Definitions and structural lemmas for Lie Trotter, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
set_option autoImplicit false
namespace QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
noncomputable def lieTrotterStep (x y : A) (z : Complex) : A :=
  NormedSpace.exp (z • x) * NormedSpace.exp (z • y)
end
end QEC.Semantics


