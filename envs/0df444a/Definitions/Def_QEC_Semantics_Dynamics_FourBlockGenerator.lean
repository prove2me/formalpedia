-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
-- name    : QEC_Semantics_Dynamics_FourBlockGenerator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:23:09.15268+00:00
-- url     : https://prove2.me/theorems/9e042eb9-dbe2-4a8a-9020-24e536f3b745
-- title:
--   Four Block Generator
-- statement:
--   Definitions and structural lemmas for Four Block Generator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_smul
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
universe u v
namespace QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
def TraceNormedOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H] := Operator H
instance : AddCommGroup (TraceNormedOperator H) :=
  inferInstanceAs (AddCommGroup (Operator H))
instance : Module ℂ (TraceNormedOperator H) :=
  inferInstanceAs (Module ℂ (Operator H))
def traceNormedOperatorSeminorm : AddGroupSeminorm (TraceNormedOperator H) where
  toFun A := traceNorm (H := H) A
  map_zero' := (traceNorm_eq_zero_iff (H := H) 0).2 rfl
  neg' := traceNorm_neg
  add_le' := traceNorm_add_le
instance traceNormedOperatorSeminormedAddCommGroup :
    SeminormedAddCommGroup (TraceNormedOperator H) :=
  traceNormedOperatorSeminorm.toSeminormedAddCommGroup
instance traceNormedOperatorNormedAddCommGroup :
    NormedAddCommGroup (TraceNormedOperator H) :=
  NormedAddCommGroup.ofSeparation fun A hA =>
    (traceNorm_eq_zero_iff (H := H) A).1 hA
instance traceNormedOperatorNormedSpace :
    NormedSpace ℂ (TraceNormedOperator H) where
  norm_smul_le c A := by
    change traceNorm (c • (A : Operator H)) ≤ ‖c‖ * traceNorm (A : Operator H)
    exact le_of_eq (traceNorm_smul c A)
def traceNormedOperatorToOperator :
    TraceNormedOperator H →ₗ[ℂ] Operator H :=
  LinearMap.id
instance traceNormedOperatorFiniteDimensional :
    FiniteDimensional ℂ (TraceNormedOperator H) :=
  FiniteDimensional.of_injective traceNormedOperatorToOperator
    (LinearMap.ker_eq_bot.mp rfl)
noncomputable def traceNormContinuousSuperoperator (L : Superoperator H) :
    TraceNormedOperator H →L[ℂ] TraceNormedOperator H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => L A
      map_add' := by intro A B; exact L.map_add A B
      map_smul' := by intro c A; exact L.map_smul c A }
def JumpProtected [Fintype ι]
    (J : ι → Operator H) (O P : Operator H) : Prop :=
  ∀ a, (J a * O - O * J a) * P = 0
def clbtGeneratorBlockOne (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  P * L (O * P * rho)
def clbtGeneratorBlockTwo (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  (1 - P) * L (O * P * rho)
def clbtGeneratorBlockThree (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  P * L (O * (1 - P) * rho)
def clbtGeneratorBlockFour (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  (1 - P) * L (O * (1 - P) * rho)
def clbtGibbsTailMass (P : Operator H) (rho : DensityOperator H) : Real :=
  Complex.re (LinearMap.trace ℂ H ((1 - P) * rho.toOperator))
end
end QEC.Semantics


