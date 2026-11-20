-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:34:57.227094+00:00
-- url     : https://prove2.me/theorems/47afd553-8a11-43b9-9117-9583a556bdb8
-- title:
--   LPSOriginal Relative Gauss Second Branches
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Second Branches, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
def lpsOriginalRelativeGaussNormalizationLinearBranchMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (RingHom.fst _ _).comp
    ((lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (Ideal.Quotient.mk _))
def lpsOriginalRelativeGaussNormalizationInseparableBranchMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (RingHom.snd _ _).comp
    ((lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (Ideal.Quotient.mk _))
end
end QEC.Coding.TannerLiftedProduct


