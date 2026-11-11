-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
-- name    : QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:04:01.666528+00:00
-- url     : https://prove2.me/theorems/ece83e0d-e89e-4122-b7df-f76ecc2415da
-- title:
--   Transposed Stopped Decoder
-- statement:
--   Definitions and structural lemmas for Transposed Stopped Decoder, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_syndrome
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dual_coboundary1_xSyndrome
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
def dualBase (S : OddScale) (n : Nat) :
    AuditedBaseDecoder (LevelTwoHistory.suffixData (dualDecoderData S (n + 2))) :=
  LevelTwoHistory.suffixBase _ (fun sigma => dualBaseDecode S sigma.val) (by
    intro sigma
    have hs : sigma.val ∈ LinearMap.range
        ((dualFamily S (n + 2)).coboundary1
          (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) := sigma.property
    obtain ⟨w,hw⟩ := hs
    have hd := dualFamily_coboundary1 S (n + 2)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))
    exact (LinearMap.congr_fun hd _).trans
      (dualBaseDecode_syndrome S sigma.val
        ⟨w,(LinearMap.congr_fun hd w).symm.trans hw⟩))
def dualHistory (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    CorrectionHistory (LevelTwoHistory.suffixData (dualDecoderData S (n + 2))) :=
  LevelTwoHistory.stoppedHistory _ (dualAboveTwoSteps S n) (dualBase S n) sigma
abbrev XSyndromeDomain (S : OddScale) (n : Nat) := LinearMap.range (zSyndrome S (n + 2))
abbrev ZSyndromeDomain (S : OddScale) (n : Nat) := LinearMap.range (xSyndrome S (n + 2))
def xCorrection (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    Word BDL26Field (Physical S (n + 2)) := by
  let sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)) := ⟨u.val,by
    change u.val ∈ LinearMap.range
      ((indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
    obtain ⟨w,hw⟩ := u.property
    exact ⟨w,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans hw⟩⟩
  exact historyLiftedCorrection (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2)))
    (BDL26OwnerIncidenceMasks.actualHistory S n sigma)
def zCorrection (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n) :
    Word BDL26Field (Physical S (n + 2)) := by
  let sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2)) := ⟨v.val,by
    change v.val ∈ LinearMap.range
      ((dualFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,((LinearMap.congr_fun
      (dualFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans
      (LinearMap.congr_fun (dual_coboundary1_xSyndrome S (n + 2)) w)).trans hw⟩⟩
  exact historyLiftedCorrection (LevelTwoHistory.suffixData (dualDecoderData S (n + 2)))
    (dualHistory S n sigma)
theorem source_even_level (k : Nat) (hk : 1 ≤ k) : 2 * (k - 1) + 2 = 2 * k := by omega
def zCorrectionEven (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (v : LinearMap.range (xSyndrome S (2 * k))) : Word BDL26Field (Physical S (2 * k)) :=
  cast (congrArg (fun m => Word BDL26Field (Physical S m)) (source_even_level k hk))
    (zCorrection S (2 * (k - 1))
      (cast (congrArg (fun m => ↥(LinearMap.range (xSyndrome S m)))
        (source_even_level k hk)).symm v))
def translateX (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (a : Word BDL26Field (Physical S (n + 2))) : XSyndromeDomain S n :=
  ⟨u.val + zSyndrome S (n + 2) a,by
    obtain ⟨w,hw⟩ := u.property
    exact ⟨w+a,by rw [map_add,hw]⟩⟩
def translateZ (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n)
    (b : Word BDL26Field (Physical S (n + 2))) : ZSyndromeDomain S n :=
  ⟨v.val + xSyndrome S (n + 2) b,by
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w+b,by rw [map_add,hw]⟩⟩
def pairedCorrection (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) : Binary (Physical S (n + 2)) :=
  binaryMul (cssXCheck (xCorrection S n u)) (cssZCheck (zCorrection S n v))
def pairedResidual (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) : Binary (Physical S (n + 2)) :=
  binaryMul (pairedCorrection S n (translateX S n u E.vector.xPart)
      (translateZ S n v E.vector.zPart)) (binaryMul E (pairedCorrection S n u v))
def basisTranslations (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (q : Physical S (n + 2)) (a : CSSDaviesLocality.Axis) :=
  (translateX S n u (CSSDaviesLocality.singlePauli q a).vector.xPart,
    translateZ S n v (CSSDaviesLocality.singlePauli q a).vector.zPart)
end QEC.Coding.BDL26TransposedStoppedDecoder
end


