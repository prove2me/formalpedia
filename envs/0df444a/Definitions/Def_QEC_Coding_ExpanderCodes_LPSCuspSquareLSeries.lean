-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
-- name    : QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:42:10.221196+00:00
-- url     : https://prove2.me/theorems/7c383e27-cef8-4a1b-bf40-eea27f590299
-- title:
--   LPSCusp Square LSeries
-- statement:
--   Definitions and structural lemmas for LPSCusp Square LSeries, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable def lpsWeightTwoCusp_squareCoeff (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) : ℝ :=
  ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2
noncomputable def lpsCuspHorocycleSquareMean (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (y : ℝ) : ℝ :=
  ∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle
end QEC.Coding.TannerLiftedProduct


