-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T14:01:36.717184+00:00
-- url     : https://prove2.me/theorems/bf6b8971-7d72-4cec-b2c9-423c53363b00
-- title:
--   Physical CCZ
-- statement:
--   Definitions and structural lemmas for Physical CCZ, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_coordinateSupport_disjoint

set_option autoImplicit false
noncomputable section
namespace QEC.Distillation
open Semantics
open scoped BigOperators
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
noncomputable def taggedCczSiteEquivFin (ι : Type u) [Fintype ι] :
    Fin (Fintype.card ι) ≃ ι :=
  (Fintype.equivFin ι).symm
noncomputable def taggedCczPhysicalTransport [Fintype ι] [DecidableEq ι] :
    UnitaryTransport (TaggedThreeCopyRegister F ι) (TaggedThreeCopyRegister F ι) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card ι) =>
    taggedCczTransport (taggedCczSiteEquivFin ι j)
inductive TaggedCczLocalGate [Fintype ι] [DecidableEq ι] :
    Finset (TaggedThreeCopyCoordinate ι) → Type u
  | at (site : ι) : TaggedCczLocalGate (coordinateSupport site)
noncomputable def taggedCczPhysicalGateModel [Fintype ι] [DecidableEq ι] :
    FinitePhysicalGateModel (TaggedThreeCopyCoordinate ι)
      (TaggedThreeCopyRegister F ι) where
  LocalGate := TaggedCczLocalGate
  realize gate := match gate with
    | .at site => taggedCczTransport site
noncomputable def taggedCczPhysicalFactorization [Fintype ι] [DecidableEq ι] :
    PhysicalGateFactorization (taggedCczPhysicalGateModel (F := F) (ι := ι))
      (taggedCczPhysicalTransport (F := F) (ι := ι)) where
  factorCount := Fintype.card ι
  support j := coordinateSupport (taggedCczSiteEquivFin ι j)
  factor j := .at (taggedCczSiteEquivFin ι j)
  pairwise_disjoint := by
    intro i j hij
    exact coordinateSupport_disjoint
      ((taggedCczSiteEquivFin ι).injective.ne hij)
  realizes := rfl
end QEC.Distillation


