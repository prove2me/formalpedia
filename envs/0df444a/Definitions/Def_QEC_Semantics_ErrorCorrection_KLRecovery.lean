-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
-- name    : QEC_Semantics_ErrorCorrection_KLRecovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:38:35.518012+00:00
-- url     : https://prove2.me/theorems/8d6ecfa3-68dc-4a75-9a46-8fc18cac4d88
-- title:
--   KLRecovery
-- statement:
--   Definitions and structural lemmas for KLRecovery, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
set_option autoImplicit false
universe u v w
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
section IndexUnitaryMix
variable [DecidableEq ι]
noncomputable def indexMix
    (E : FiniteKrausFamily ι H H) (U : Matrix ι ι Complex) :
    FiniteKrausFamily ι H H where
  operator a := ∑ i : ι, U i a • E.operator i
noncomputable def indexUnitaryMix
    (E : FiniteKrausFamily ι H H) (U : Matrix.unitaryGroup ι Complex) :
    FiniteKrausFamily ι H H :=
  E.indexMix (U : Matrix ι ι Complex)
end IndexUnitaryMix
section DiagonalRecovery
variable [DecidableEq ι]
noncomputable def diagonalRecoveryOperator
    (C : QuantumCode H) (F : FiniteKrausFamily ι H H) (lambda : ι → ℝ)
    (i : ι) : Operator H :=
  if lambda i = 0 then 0
  else ((Real.sqrt (lambda i) : Complex)⁻¹) •
    C.projector.comp (LinearMap.adjoint (F.operator i))
end DiagonalRecovery
end FiniteKrausFamily
end
end Semantics
end QEC


