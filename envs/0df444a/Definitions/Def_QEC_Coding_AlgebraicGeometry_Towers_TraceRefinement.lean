-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:09:56.77294+00:00
-- url     : https://prove2.me/theorems/90b1466a-6f33-4d8e-ace4-fee3c9f59168
-- title:
--   Trace Refinement
-- statement:
--   Definitions and structural lemmas for Trace Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/TraceRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
def tracePrefixField (K : IntermediateField F E) (t : ℕ → E) : ℕ → IntermediateField F E
  | 0 => K
  | j + 1 => ((tracePrefixField K t j)⟮t (j + 1)⟯).restrictScalars F
theorem tracePrefixField_coordinate_mem
    (K : IntermediateField F E) (t : ℕ → E) (ht : t 0 ∈ K) (j : ℕ) :
    t j ∈ tracePrefixField K t j := by
  cases j with
  | zero => exact ht
  | succ j => exact IntermediateField.mem_adjoin_simple_self (tracePrefixField K t j) (t (j + 1))
def traceCoordinates16 (y : E) : ℕ → E
  | 0 => y ^ 16 + y
  | 1 => y ^ 8 + y ^ 4 + y ^ 2 + y
  | 2 => y ^ 4 + y
  | 3 => y ^ 2 + y
  | _ => y
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "P" => IntermediateIntegralModels.prime A F E Q
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


