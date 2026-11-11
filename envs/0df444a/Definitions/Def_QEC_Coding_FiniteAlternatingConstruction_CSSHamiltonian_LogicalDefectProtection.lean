-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T19:07:38.015252+00:00
-- url     : https://prove2.me/theorems/488a50ab-5cc3-4926-8539-abb9f1cde0a1
-- title:
--   Logical Defect Protection
-- statement:
--   Definitions and structural lemmas for Logical Defect Protection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
local instance _p2m_local_instance_6c2d909602_23 : Fintype (XSyndromeDomain S n) := Fintype.ofFinite _
local instance _p2m_local_instance_6c2d909602_24 : Fintype (ZSyndromeDomain S n) := Fintype.ofFinite _
abbrev W := Word (ZMod 2) (Physical S (n+2))
abbrev xWord : W S n := (BDL26BareLogicalPair.canonicalGenerator S (n+2)).val
abbrev zWord : W S n := BDL26BareLogicalPair.partnerWord S (n+2)
abbrev xRows := (parityCheckRowCode (xSyndrome S (n+2))).carrier
abbrev zRows := (parityCheckRowCode (zSyndrome S (n+2))).carrier
def h1Coordinate (a : BDL26FiniteCohomology.Cocycle S (n+2)) : ZMod 2 :=
  BDL26FiniteCohomology.finiteH1Equiv S (n+2)
    (BDL26FiniteCohomology.classOf S (n+2) a)
def dX (s : Visible S n) (E : Binary (Physical S (n+2))) : ZMod 2 :=
  wordPairing (residual S n s E).vector.xPart (zWord S n)
def dZ (s : Visible S n) (E : Binary (Physical S (n+2))) : ZMod 2 :=
  wordPairing (xWord S n) (residual S n s E).vector.zPart
def coefficient (s : Visible S n) (E L : Binary (Physical S (n+2))) : ℂ :=
  commutationPhase E L * commutationPhase (correction S n s) L -
    commutationPhase (correction S n (translation S n E s)) L
def deltaX (u : XSyndromeDomain S n) (q : Physical S (n+2)) : W S n :=
  xCorrection S n (translateX S n u (Pi.single q 1)) + Pi.single q 1 + xCorrection S n u
def deltaZ (v : ZSyndromeDomain S n) (q : Physical S (n+2)) : W S n :=
  zCorrection S n (translateZ S n v (Pi.single q 1)) + Pi.single q 1 + zCorrection S n v
def chiX (u : XSyndromeDomain S n) (q : Physical S (n+2)) : ZMod 2 :=
  wordPairing (deltaX S n u q) (zWord S n)
def chiZ (v : ZSyndromeDomain S n) (q : Physical S (n+2)) : ZMod 2 :=
  wordPairing (xWord S n) (deltaZ S n v q)
def goodX : Finset (XSyndromeDomain S n) := Finset.univ.filter (fun u => ∀ q, chiX S n u q = 0)
def goodZ : Finset (ZSyndromeDomain S n) := Finset.univ.filter (fun v => ∀ q, chiZ S n v q = 0)
def good : Finset (Visible S n) := goodX S n ×ˢ goodZ S n
def protectedProjector : BDL26PairedDecoderChannel.Op S n :=
  BDL26TwoSectorBadProjector.selected S (n+2) (good S n)
def Protects (A : Finset (Visible S n)) : Prop := ∀ q axis,
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        BDL26TwoSectorBadProjector.selected S (n+2) A = 0 ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        BDL26TwoSectorBadProjector.selected S (n+2) A = 0
def badX : Finset (XSyndromeDomain S n) := (goodX S n)ᶜ
def badZ : Finset (ZSyndromeDomain S n) := (goodZ S n)ᶜ
end QEC.Coding.BDL26LogicalDefectProtection
end


