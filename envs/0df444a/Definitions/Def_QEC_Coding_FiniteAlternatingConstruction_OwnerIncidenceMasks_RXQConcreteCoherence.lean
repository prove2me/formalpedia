-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T07:32:05.04267+00:00
-- url     : https://prove2.me/theorems/5dff3c94-5bd0-4730-886c-6d55f800ff58
-- title:
--   RXQConcrete Coherence
-- statement:
--   Definitions and structural lemmas for RXQConcrete Coherence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXQConcreteCoherence.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_componentOwner_bijective
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incidentWitness_mem
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_componentOwner_bijective
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
theorem successor_eq (h : i.val%2=0) :
    state S (i.val+1)=rxState S (state S i.val) := by
  change nextState S i.val (state S i.val)=_
  exact if_pos h
def physicalZEquiv (h : i.val%2=0) :
    RX2 (state S i.val).presentation S ≃ FamilyZ S depth i.succ :=
  Equiv.cast (congrArg (fun C : ConstructionState => C.presentation.Z)
    (successor_eq S depth i h)).symm
def qComponentIndex (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    Fin (rxStepOutput S depth i h sigma).localComponents.length :=
  Classical.choose ((componentOwner_bijective S depth i h sigma).2 (.inr (.inl q)))
def basisImage (q : (state S i.val).presentation.Q) : Word BDL26Field (FamilyZ S depth i.succ) :=
  ((indexedDecoderData S depth).selectedMap i).map2
    ((indexedFamily S depth).coboundary1 i.castSucc (canonicalBasisWord q))
theorem basisImage_native_syndrome (q : (state S i.val).presentation.Q) :
    basisImage S depth i q=(indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q)) := by
  exact (LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (canonicalBasisWord (F:=BDL26Field) q)).symm
def basisInput (q : (state S i.val).presentation.Q) : (indexedFamily S depth).Syndrome i.succ :=
  ⟨basisImage S depth i q,⟨((indexedDecoderData S depth).selectedMap i).map1
    (canonicalBasisWord q),(basisImage_native_syndrome S depth i q).symm⟩⟩
def connectorEdge (q : (state S i.val).presentation.Q) :
    QDoubleCylinderEdge (state S i.val).presentation q S :=
  .inl (0,⟨BDL26RXQBlockTransport.incidentWitness S i q,
    BDL26RXQBlockTransport.incidentWitness_mem S i q⟩,⟨0,S.half_pos⟩)
def connector (h : i.val%2=0) (q : (state S i.val).presentation.Q) : FamilyZ S depth i.succ :=
  physicalZEquiv S depth i h (.inl (.inr ⟨q,connectorEdge S depth i q⟩))
end QEC.Coding.BDL26RXQConcreteCoherence
end


