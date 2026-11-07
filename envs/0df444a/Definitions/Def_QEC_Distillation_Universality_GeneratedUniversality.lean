-- Prove2me | Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
-- name    : QEC_Distillation_Universality_GeneratedUniversality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:42:48.162697+00:00
-- url     : https://prove2.me/theorems/b8518c17-24e6-4d0c-9442-ad0b6e5b87b0
-- title:
--   Generated Universality
-- statement:
--   Definitions and structural lemmas for Generated Universality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
set_option autoImplicit false
noncomputable section
universe u
namespace QEC
namespace Distillation
namespace GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise
abbrev UnitaryGate (n : Type u) [Fintype n] [DecidableEq n] :=
  Matrix.unitaryGroup n Complex
def GlobalPhaseEquivalent {n : Type u} [Fintype n] [DecidableEq n]
    (U V : UnitaryGate n) : Prop :=
  ∃ scalar : Complex, ‖scalar‖ = 1 ∧
    (V : Matrix n n Complex) = scalar • (U : Matrix n n Complex)
def generatedUnitarySubgroup {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) : Subgroup (UnitaryGate n) :=
  Subgroup.closure generators
def generatedUnitaryTopologicalClosure {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) : Set (UnitaryGate n) :=
  closure (generatedUnitarySubgroup generators : Set (UnitaryGate n))
def GeneratedUnitaryDense {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) : Prop :=
  generatedUnitaryTopologicalClosure generators = Set.univ
def ProjectivelyGeneratedDense {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) : Prop :=
  ∀ target : UnitaryGate n, ∃ representative : UnitaryGate n,
    representative ∈ generatedUnitaryTopologicalClosure generators ∧
      GlobalPhaseEquivalent target representative
def ApproximatesModuloPhase {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) (target : UnitaryGate n) (precision : Real) : Prop :=
  ∃ candidate : UnitaryGate n,
    candidate ∈ generatedUnitaryTopologicalClosure generators ∧
      ∃ scalar : Complex, ‖scalar‖ = 1 ∧
        ‖(candidate : Matrix n n Complex) - scalar • (target : Matrix n n Complex)‖ < precision
def FinitePrecisionUniversal {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) : Prop :=
  ∀ target : UnitaryGate n, ∀ precision : Real, 0 < precision →
    ApproximatesModuloPhase generators target precision
def FinitePrecisionOneQubitUniversal
    (generators : Set (UnitaryGate (Fin 2))) : Prop :=
  FinitePrecisionUniversal generators
def FinitePrecisionRegisterUniversal (r : Nat)
    (generators : Set (UnitaryGate (Fin (2 ^ r)))) : Prop :=
  FinitePrecisionUniversal generators
noncomputable def transportDensity {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (U : UnitaryTransport H H) (rho : DensityOperator H) : DensityOperator H :=
  U.conjDensity rho
end GeneratedUniversality
end Distillation
end QEC


