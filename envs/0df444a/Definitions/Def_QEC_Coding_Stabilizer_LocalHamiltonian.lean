-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
-- name    : QEC_Coding_Stabilizer_LocalHamiltonian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:48:51.125256+00:00
-- url     : https://prove2.me/theorems/ccd48e35-1707-4cd8-b0fa-8367e47fb0b6
-- title:
--   Local Hamiltonian
-- statement:
--   Definitions and structural lemmas for Local Hamiltonian, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
structure LocalStabilizerHamiltonian where
  code : SourceValidBinary ι
  generators : κ → Binary ι
  generated_eq : generatedStabilizerSet generators = code.1.generatedGroup
  generator_self_adjoint : ∀ j,
    LinearMap.adjoint (toQubitOperator (generators j)) =
      toQubitOperator (generators j)
  geometry : Locality.LatticeGeometry ι
  interactionRange : Nat
  interactionRange_positive : 0 < interactionRange
  local_support : ∀ j,
    Locality.BoundedDiameter geometry (support (generators j) : Set ι)
      interactionRange
  participationBound : Nat
  participationBound_positive : 0 < participationBound
  participation_le : ∀ i,
    (Finset.univ.filter fun j => i ∈ support (generators j)).card ≤
      participationBound
namespace LocalStabilizerHamiltonian
def generatorSupport (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (j : κ) : Finset ι :=
  support (H.generators j)
def interactionGraph
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    Locality.ConnectivityGraph ι :=
  fixedGeneratorInteractionGraphOf H.generators
def incidentGenerators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (i : ι) : Finset κ :=
  Finset.univ.filter fun j => i ∈ H.generatorSupport j
noncomputable def generatorOperator
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  toQubitOperator (H.generators j)
noncomputable def term
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  -(H.generatorOperator j)
noncomputable def operator
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  ∑ j, H.term j
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


