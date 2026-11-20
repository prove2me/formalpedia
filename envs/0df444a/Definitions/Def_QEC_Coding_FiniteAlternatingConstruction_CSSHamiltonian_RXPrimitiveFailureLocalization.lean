-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:19:30.397816+00:00
-- url     : https://prove2.me/theorems/f36caad1-004d-4fe6-ad4a-b73bd88d7246
-- title:
--   RXPrimitive Failure Localization
-- statement:
--   Definitions and structural lemmas for RXPrimitive Failure Localization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_base_calls
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_terminal_syndrome
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSuccess_iff
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_zero_branch
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_c2_face_local
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_c2_singleton_local
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_parser_semantics
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
theorem zero_boundary (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    (SuffixData S N).family.coboundary0 a 0=
      (BDL26BoundaryTailInvariance.snapshot S N u q a).word :=
  (map_zero _).trans hz.symm
theorem zero_base_calls (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :
    firstReadout S N u=secondReadout S N u q ∧
      (actualBase S N).decode (actualInputs S N (input S N u) 0)=
        (actualBase S N).decode
          (actualInputs S N (perturbTop S N (input S N u) (flip S N q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S N u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S N u q) :=
  BDL26BoundaryTailInvariance.physical_base_calls S N u q a 0
    (zero_boundary S N u q a hz)
def zeroFullPotential (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : LevelIndex N)
    (hz : (BDL26BoundaryTailInvariance.snapshot S N u q a).word=0) :=
  BDL26BoundaryTailInvariance.physicalPotential S N u q a 0 (zero_boundary S N u q a hz)
theorem safe_search (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S N u q) := by
  have hm := parser_semantics S N u q
  cases hl : parse S N q with
  | c2 r =>
    rw [hl] at hm
    have he := c2_singleton_local S N u q r hm
    apply (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    exact ⟨(descent S N u q).word,he,
      BDL26FirstZeroFaceEndpoint.terminal_syndrome S N u q hs⟩
  | face a =>
    rw [hl] at hm
    have he := c2_face_local S N u q a hm
    apply (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    exact ⟨(descent S N u q).word,he,
      BDL26FirstZeroFaceEndpoint.terminal_syndrome S N u q hs⟩
  | killed b =>
    rw [hl] at hm
    obtain ⟨hb,hz⟩ := hm
    have hc := (zero_base_calls S N u q ⟨b,Nat.lt_succ_of_le hb⟩ hz).1
    have ht : secondReadout S N u q=0 := hc.symm.trans hs
    rw [ht]
    exact BDL26LevelTwoLocalBranchEndpoint.zero_branch S
  | primitive p =>
    rw [hl] at hSafe
    cases hSafe
def safeFullPotential (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hSafe : (parse S N q).safe=true) :=
  BDL26LocalSearchFailureReduction.fullPotential S N u q hs (safe_search S N u q hs hSafe)
def primitiveEvent (S : OddScale) (N : Nat) : Finset (XSyndromeDomain S N) :=
  Finset.univ.filter (fun u => firstReadout S N u=0 ∧
    ∃ (q : Physical S (N+2)) (b : Nat) (hb : b≤N) (p : Primitive S b),
      parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical)
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26RXPrimitiveFailureLocalization


