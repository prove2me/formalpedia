-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
-- name    : QEC_Semantics_ErrorCorrection_QuditNoInformation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:48:27.50276+00:00
-- url     : https://prove2.me/theorems/8f5b749c-180b-4a25-ae94-f988f9184a90
-- title:
--   Qudit No Information
-- statement:
--   Definitions and structural lemmas for Qudit No Information, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
def ValidEffect {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (E : Operator H) : Prop :=
  LinearMap.IsPositive E ∧ LinearMap.IsPositive ((1 : Operator H) - E)
def FinitePOVM {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {m : Type v} [Fintype m]
    (effects : m → Operator H) : Prop :=
  (∀ i, ValidEffect (effects i)) ∧ ∑ i, effects i = 1
namespace QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
def ScalarCompression (C : QuantumCode (Qudit.QuditRegister q))
    (A : Operator (Qudit.QuditRegister q)) : Prop :=
  ∃ scalar : Complex,
    C.projector.comp (A.comp C.projector) = scalar • C.projector
def AllLocalScalarCompression (C : QuantumCode (Qudit.QuditRegister q))
    (S : QuditSubsystem q) : Prop :=
  ∀ A : Operator S.selectedSystem,
    ScalarCompression C (S.extendLocalToRegister A)
def NoInformationOn (C : QuantumCode (Qudit.QuditRegister q))
    (S : QuditSubsystem q) : Prop :=
  ∀ E : Operator S.selectedSystem, ValidEffect E →
    ScalarCompression C (S.extendLocalToRegister E)
def FinitePOVMDistributionInvariant (C : QuantumCode (Qudit.QuditRegister q))
    (S : QuditSubsystem q) : Prop :=
  ∀ (m : Type v) (_ : Fintype m) (effects : m → Operator S.selectedSystem),
    FinitePOVM effects →
      ∀ i : m, ∀ rho sigma : DensityOperator (Qudit.QuditRegister q),
        DensityOperator.SupportedOn C rho → DensityOperator.SupportedOn C sigma →
          LinearMap.trace Complex (Qudit.QuditRegister q)
              ((S.extendLocalToRegister (effects i)).comp rho.toOperator) =
            LinearMap.trace Complex (Qudit.QuditRegister q)
              ((S.extendLocalToRegister (effects i)).comp sigma.toOperator)
noncomputable def replacementFactorizedKraus (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    FiniteKrausFamily
      (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem))
      S.factorizedSystem S.factorizedSystem := by
  let b : OrthonormalBasis (Fin (Module.finrank Complex S.selectedSystem)) Complex S.selectedSystem :=
    stdOrthonormalBasis Complex S.selectedSystem
  exact {
    operator := fun p =>
      (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch (b p.2))) }
noncomputable def replacementKraus (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    FiniteKrausFamily
      (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem))
      (Qudit.QuditRegister q) (Qudit.QuditRegister q) :=
  (S.replacementFactorizedKraus rho).unitaryTransport
    S.registerFactorization.symm S.registerFactorization.symm
def BPTMeasurementDistance (C : QuantumCode (Qudit.QuditRegister q)) (d : Nat) : Prop :=
  ∀ S : QuditSubsystem q, Fintype.card S.SelectedCoordinates < d → NoInformationOn C S
end QuditSubsystem
end Semantics
end QEC


