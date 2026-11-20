-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:31:41.634067+00:00
-- url     : https://prove2.me/theorems/d48c2e9b-a674-4d08-9cc0-ec1fdd324e29
-- title:
--   First Zero Face Endpoint
-- statement:
--   Definitions and structural lemmas for First Zero Face Endpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelOne_two_support_cocycle_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_add_qParity_two_coordinates
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_cocycle
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSuccess_iff
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_mem_physicalXStar
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.mem_physicalXStar


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
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
abbrev Error (S : OddScale) := Word F (C S).Q
abbrev Syndrome (S : OddScale) := Word F (C S).Z
abbrev Potential (S : OddScale) := Word F (C S).X
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
abbrev parity (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.parity S
def faceSupported (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S) : Prop :=
  hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
    (C S) (.inl (.inl ⟨z,f⟩))
theorem face_owner (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) (r : RZQ (P S) S) (hr : h r≠0) :
    BDL26ReplacementSupport.rzCorrectionOwner (P S) S r=Vertex.z z := by
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp
    (hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩))
  change rzXQIncidence (P S) (rxState S baseState).admissible.toTannerSquareAdmissible S
    (.inl (.inl ⟨z,f⟩)) r=true at hi
  rcases r with ⟨z',edge⟩ | ⟨q,v⟩
  · change decide (∃ hz : z'=z,
      doubleCylinderFaceEdgeMatrix (transposePresentation (P S)) z S
        (hz ▸ edge) f=1)=true at hi
    obtain ⟨hz,_⟩ := of_decide_eq_true hi
    change Vertex.z z'=Vertex.z z
    exact congrArg Vertex.z hz
  · change false=true at hi
    contradiction
theorem face_local (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : levelTwoLocalError S h := by
  apply (levelTwoLocalError_iff_owner S h).mpr
  exact ⟨Vertex.z z,face_owner S z f h hh⟩
theorem face_search (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (delta S h) :=
  (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨h,face_local S z f h hh,rfl⟩
def faceResidual (S : OddScale) (h : Error S) : Error S := h+D S 0+D S (delta S h)
theorem twice {I : Type} (w : Word F I) : w+w=0 := by
  funext i
  exact ZModModule.add_self (w i)
theorem q_parity_heq {U V : TannerSquarePresentation} (e : U=V) (S : OddScale) :
    HEq (rzQParity U S) (rzQParity V S) := by
  cases e
  rfl
theorem levelOne_parity (S : OddScale) :
    (rzQParity (levelOnePresentation S) S : Error S →ₗ[F] Word F (P S).Q)=parity S :=
  eq_of_heq (q_parity_heq
    (show levelOnePresentation S=BDL26LevelTwoLocalBranchEndpoint.P S from rfl) S)
theorem face_residual_closed (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : delta S (faceResidual S h)=0 := by
  obtain ⟨w,hw⟩ := face_search S z f h hh
  have hd : delta S (D S (delta S h))=delta S h :=
    (BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw).2
  have hz : D S (0 : Syndrome S)=0 := BDL26LevelTwoLocalBranchEndpoint.decode_zero S
  change delta S (h+D S 0+D S (delta S h))=0
  rw [hz,add_zero,map_add,hd]
  exact twice _
theorem face_residual_parity (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : parity S (faceResidual S h)=0 := by
  obtain ⟨w,hw⟩ := face_search S z f h hh
  have hl := (BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S _ w hw).1
  obtain ⟨a,b,hab⟩ := levelTwoLocalError_add_qParity_two_coordinates S
    (levelOneQDefault S) h (D S (delta S h)) (face_local S z f h hh) hl
  have hc := face_residual_closed S z f h hh
  have hp := rzQParity_cocycle (P S) (rxState S baseState).admissible S (faceResidual S h) hc
  have hz : D S (0 : Syndrome S)=0 := BDL26LevelTwoLocalBranchEndpoint.decode_zero S
  have hr : faceResidual S h=h+D S (delta S h) := by
    change h+D S 0+D S (delta S h)=h+D S (delta S h)
    rw [hz,add_zero]
  apply levelOne_two_support_cocycle_zero S _ hp a b
  intro q hq
  apply hab q
  have hq' : parity S (h+D S (delta S h)) q≠0 := by
    intro hzero
    exact hq ((congrArg (fun r : Error S => parity S r q) hr).trans hzero)
  have hvalue := congrArg (fun op : Error S →ₗ[F] Word F (P S).Q =>
    op (h+D S (delta S h)) q) (levelOne_parity S)
  exact fun hzero => hq' (hvalue.symm.trans hzero)
theorem face_full_filling (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    ∃ pQ pZ : Potential S,
      (∀ q v, boundary S pQ (.inr ⟨q,v⟩)=faceResidual S h (.inr ⟨q,v⟩)) ∧
      (∀ q v, (faceResidual S h+boundary S pQ) (.inr ⟨q,v⟩)=0) ∧
      boundary S pZ=faceResidual S h+boundary S pQ ∧
      boundary S (pZ+pQ)=faceResidual S h :=
  BDL26LevelTwoLocalBranchEndpoint.full_filling S _
    (face_residual_closed S z f h hh) (face_residual_parity S z f h hh)
def faceQPotential (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : Potential S :=
  Classical.choose (face_full_filling S z f h hh)
def faceZPotential (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : Potential S :=
  Classical.choose (Classical.choose_spec (face_full_filling S z f h hh))
def facePotential (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : Potential S :=
  faceZPotential S z f h hh+faceQPotential S z f h hh
def terminalFace (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S) : Prop :=
  (descent S n u q).center=(.inl (.inl ⟨z,f⟩) : (state S 2).presentation.X)
theorem presentation_operations_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar U)
      (BDL26RXPhysicalStarTransport.physicalXStar V) ∧
    HEq (fun w : Word F U.Q => hammingSupport w)
      (fun w : Word F V.Q => hammingSupport w) ∧
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) ∧
    HEq (tannerCoboundary1 U) (tannerCoboundary1 V) := by
  cases e
  exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩
theorem actual_presentation (S : OddScale) : (state S 2).presentation=C S :=
  congrArg ConstructionState.presentation (levelTwoState_eq_pair S)
theorem terminal_supported (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hf : terminalFace S n u q z f) : faceSupported S z f (descent S n u q).word := by
  have hm := presentation_operations_heq (actual_presentation S)
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (C S).X → Finset (C S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (C S) :=
    eq_of_heq hm.1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      Error S → Finset (C S).Q)=(fun w : Error S => hammingSupport w) :=
    eq_of_heq hm.2.1
  have hh := descent_supported S n u q
  change (fun w : Word F (state S 2).presentation.Q => hammingSupport w)
      (descent S n u q).word ⊆
    BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation (descent S n u q).center at hh
  change (descent S n u q).center=(.inl (.inl ⟨z,f⟩) : (C S).X) at hf
  rw [hf] at hh
  have hhs := congrArg (fun support : Error S → Finset (C S).Q =>
    support (descent S n u q).word) hsupport
  have hxs := congrArg (fun star : (C S).X → Finset (C S).Q =>
    star (.inl (.inl ⟨z,f⟩))) hstar
  intro r hr
  have hri := Eq.mpr (congrArg (fun t : Finset (C S).Q => r ∈ t) hhs) hr
  have hro := hh hri
  exact Eq.mp (congrArg (fun t : Finset (C S).Q => r ∈ t) hxs) hro
def baseFacePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hf : terminalFace S n u q z f) : (SuffixData S n).family.Cochain0 0 :=
  facePotential S z f (descent S n u q).word (terminal_supported S n u q z f hf)
def fullFacePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hf : terminalFace S n u q z f) : (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
    (baseFacePotential S n u q z f hf)+accumulated S n u q
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26FirstZeroFaceEndpoint


