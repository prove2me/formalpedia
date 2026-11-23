-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:53.828613+00:00
-- url     : https://prove2.me/theorems/75663617-fdd2-43f1-a57e-3991939d45e4
-- title:
--   Frobenius Of Padic
-- statement:
--   Definitions and structural lemmas for Frobenius Of Padic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOfPadic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
namespace GlobalTheory.DetInv.PsiPhi
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]
theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _
theorem frobenius_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  have key : (_root_.frobenius (PreTilt O p) p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _
def phiInvAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { phiInv p O with commutes' := fun c => phiInv_ofPadic c }
def frobAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { (WittVector.frobenius : Ainf p O →+* Ainf p O) with commutes' := fun c => frobenius_ofPadic c }
end GlobalTheory.DetInv.PsiPhi
namespace GlobalTheory.DetInv
end GlobalTheory.DetInv


