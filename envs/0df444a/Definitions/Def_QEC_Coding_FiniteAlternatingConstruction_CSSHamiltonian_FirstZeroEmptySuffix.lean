-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:47:42.831801+00:00
-- url     : https://prove2.me/theorems/0a98a3b8-0847-4f12-ab49-e97be0b490cf
-- title:
--   First Zero Empty Suffix
-- statement:
--   Definitions and structural lemmas for First Zero Empty Suffix, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_elementary_endpoint
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
abbrev P (S : OddScale) := RawOne S
abbrev C (S : OddScale) := RawTwo S
abbrev Error (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Error S
abbrev Potential (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Potential S
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
theorem physical_carrier (S : OddScale) : (C S).Q=Physical S 2 :=
  congrArg (fun st : ConstructionState => st.presentation.Q) (levelTwoState_eq_pair S).symm
def physicalQubit (S : OddScale) : (C S).Q ≃ Physical S 2 :=
  Equiv.cast (physical_carrier S)
def physicalWord (S : OddScale) (q : Physical S 2) : Error S := flip S 0 q
theorem physical_endpoint (S : OddScale) (q : Physical S 2) :
    ∃ p : Potential S, boundary S p=
      physicalWord S q+D S 0+D S (delta S (flip S 0 q)) := by
  obtain ⟨p,hp⟩ := BDL26LevelTwoLocalBranchEndpoint.elementary_endpoint S q
  have he := congrArg (fun w : Error S => w+D S 0+D S (delta S w))
    (flip_eq_basis S 0 q)
  exact ⟨p,hp.trans he.symm⟩
def elementaryPotential (S : OddScale) (q : Physical S 2) :
    (SuffixData S 0).family.Cochain0 0 :=
  Classical.choose (physical_endpoint S q)
def fullPotential (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2) :
    (SuffixData S 0).family.Cochain0 (TopIndex 0) :=
  intervalMap0 (SuffixData S 0) 0 (TopIndex 0) (Nat.zero_le _) (elementaryPotential S q)+
    accumulated S 0 u q
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26FirstZeroEmptySuffix


