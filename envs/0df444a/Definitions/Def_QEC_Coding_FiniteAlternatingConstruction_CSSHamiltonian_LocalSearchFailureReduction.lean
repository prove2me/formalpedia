-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:02:16.98976+00:00
-- url     : https://prove2.me/theorems/dece4e1e-8cfa-45e8-b20c-f70bffbaf0a7
-- title:
--   Local Search Failure Reduction
-- statement:
--   Definitions and structural lemmas for Local Search Failure Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_terminal_syndrome
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_edge_endpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_face_endpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_oldX_two_local_full_potential
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
abbrev C (S : OddScale) := RawTwo S
abbrev Error (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Error S
abbrev Syndrome (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Syndrome S
abbrev Potential (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.Potential S
abbrev D (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.D S
abbrev delta (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.delta S
abbrev boundary (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.boundary S
abbrev localSearch (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.localSearch S
abbrev localSuccess (S : OddScale) := BDL26LevelTwoLocalBranchEndpoint.localSuccess S
theorem returned_record (S : OddScale) (t : Syndrome S)
    (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S t=some w) :
    D S t=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S t) ∧ delta S (D S t)=t :=
  ⟨BDL26LevelTwoLocalBranchEndpoint.returned_word S t w hw,
    BDL26LevelTwoLocalBranchEndpoint.returned_local_and_syndrome S t w hw⟩
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
theorem raw_oldX_two_local (S : OddScale) :
    ∀ (x : (RawOne S).X) (c : BDL26FiniteTannerSquare.Two) (h d e : Error S),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (.inr (x,c)) →
      levelTwoLocalError S d → levelTwoLocalError S e → delta S (h+d+e)=0 →
      ∃ p : Potential S, boundary S p=h+d+e := by
  have ht : ∀ (x : (levelOnePresentation S).X) (c : BDL26FiniteTannerSquare.Two)
      (h d e : Word F (levelTwoPresentation S).Q),
      hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
        (levelTwoPresentation S) (.inr (x,c)) →
      levelTwoLocalError S d → levelTwoLocalError S e →
      tannerCoboundary1 (levelTwoPresentation S) (h+d+e)=0 →
      ∃ p : Word F (levelTwoPresentation S).X,
        tannerCoboundary0 (levelTwoPresentation S) p=h+d+e := by
    intro x c h d e hh hd he hc
    obtain ⟨g,edges,faces,hp⟩ :=
      BDL26LevelTwoOldXStarEndpoint.oldX_two_local_full_potential S x c h d e hh hd he hc
    exact ⟨_,hp⟩
  have hp : levelTwoPresentation S=C S :=
    congrArg ConstructionState.presentation (levelTwoState_eq_pair S)
  have hm := presentation_operations_heq hp
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (levelTwoPresentation S) :
      (C S).X → Finset (C S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (C S) :=
    eq_of_heq hm.1
  have hsupport : ((fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) :
      Error S → Finset (C S).Q)=(fun w : Error S => hammingSupport w) := eq_of_heq hm.2.1
  have hdelta0 : (tannerCoboundary0 (levelTwoPresentation S) :
      Potential S →ₗ[F] Error S)=boundary S := eq_of_heq hm.2.2.1
  have hdelta1 : (tannerCoboundary1 (levelTwoPresentation S) :
      Error S →ₗ[F] Syndrome S)=delta S := eq_of_heq hm.2.2.2
  intro x c h d e hh hd he hc
  have hhs := congrArg (fun support : Error S → Finset (C S).Q => support h) hsupport
  have hxs := congrArg (fun star : (C S).X → Finset (C S).Q => star (.inr (x,c))) hstar
  have hh' : (fun w : Word F (levelTwoPresentation S).Q => hammingSupport w) h ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (levelTwoPresentation S) (.inr (x,c)) := by
    intro r hr
    have hri := Eq.mp (congrArg (fun t : Finset (C S).Q => r ∈ t) hhs) hr
    exact Eq.mpr (congrArg (fun t : Finset (C S).Q => r ∈ t) hxs) (hh hri)
  have hc' : tannerCoboundary1 (levelTwoPresentation S) (h+d+e)=0 :=
    (LinearMap.congr_fun hdelta1 (h+d+e)).trans hc
  obtain ⟨p,hp⟩ := ht x c h d e hh' hd he hc'
  exact ⟨p,(LinearMap.congr_fun hdelta0 p).symm.trans hp⟩
theorem raw_star_endpoint (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) := by
  change RZX (RawOne S) S at x
  rcases x with (⟨z,f⟩ | ⟨q,e⟩) | ⟨x,c⟩
  · exact BDL26LevelTwoLocalBranchEndpoint.face_endpoint S z f h hh hb
  · exact BDL26LevelTwoLocalBranchEndpoint.edge_endpoint S q e h hh hb
  · obtain ⟨w,hw⟩ := hb
    have hr := returned_record S (delta S h) w hw
    have hz : D S (0 : Syndrome S)=(0 : Error S) :=
      BDL26LevelTwoLocalBranchEndpoint.decode_zero S
    have hd : levelTwoLocalError S (D S 0) :=
      Eq.mpr (congrArg (fun a : Error S => levelTwoLocalError S a) hz)
        (zero_original_local S)
    have hdz : delta S (D S 0)=0 := (congrArg (delta S) hz).trans (map_zero _)
    have hc : delta S (h+D S 0+D S (delta S h))=0 := by
      rw [map_add,map_add,hdz,hr.2.2,add_zero]
      exact ZModModule.add_self _
    exact raw_oldX_two_local S x c h _ _ hh hd hr.2.1 hc
def rawStarPotential (S : OddScale) (x : (C S).X) (h : Error S)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) x)
    (hb : localSuccess S (delta S h)) : Potential S :=
  Classical.choose (raw_star_endpoint S x h hh hb)
theorem terminal_supported (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) :
    hammingSupport (descent S n u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (C S) (descent S n u q).center := by
  have hm := presentation_operations_heq (actual_presentation S)
  have hstar : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (C S).X → Finset (C S).Q)=BDL26RXPhysicalStarTransport.physicalXStar (C S) :=
    eq_of_heq hm.1
  have hsupport : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      Error S → Finset (C S).Q)=(fun w : Error S => hammingSupport w) := eq_of_heq hm.2.1
  have hh := descent_supported S n u q
  change (fun w : Word F (state S 2).presentation.Q => hammingSupport w)
      (descent S n u q).word ⊆
    BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation (descent S n u q).center at hh
  have hhs := congrArg (fun support : Error S → Finset (C S).Q =>
    support (descent S n u q).word) hsupport
  have hxs := congrArg (fun star : (C S).X → Finset (C S).Q =>
    star (descent S n u q).center) hstar
  intro r hr
  have hri := Eq.mpr (congrArg (fun t : Finset (C S).Q => r ∈ t) hhs) hr
  exact Eq.mp (congrArg (fun t : Finset (C S).Q => r ∈ t) hxs) (hh hri)
theorem terminal_search (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) :
    localSuccess S (delta S (descent S n u q).word) := by
  rw [BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs]
  exact hb
def basePotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) : (SuffixData S n).family.Cochain0 0 :=
  rawStarPotential S (descent S n u q).center (descent S n u q).word
    (terminal_supported S n u q) (terminal_search S n u q hs hb)
def fullPotential (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0)
    (hb : localSuccess S (secondReadout S n u q)) : (SuffixData S n).family.Cochain0 (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
    (basePotential S n u q hs hb)+accumulated S n u q
def firstEvent (S : OddScale) (n : Nat) : Finset (XSyndromeDomain S n) :=
  Finset.univ.filter (fun u => firstReadout S n u≠0)
def searchFailureEvent (S : OddScale) (n : Nat) : Finset (XSyndromeDomain S n) :=
  Finset.univ.filter (fun u => firstReadout S n u=0 ∧
    ∃ q : Physical S (n+2), localSearch S (secondReadout S n u q)=none)
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26LocalSearchFailureReduction


