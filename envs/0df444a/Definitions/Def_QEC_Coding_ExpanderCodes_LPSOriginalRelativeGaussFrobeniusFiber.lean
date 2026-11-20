-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:34:36.53947+00:00
-- url     : https://prove2.me/theorems/fe92d278-0a9f-4d44-b3aa-2ade33575081
-- title:
--   LPSOriginal Relative Gauss Frobenius Fiber
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Frobenius Fiber, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
def lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) ≃+*
        (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
          (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  exact (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q).trans
    (RingEquiv.prodCongr (RingEquiv.refl K)
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q))
lemma lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c)) =
        ((Ideal.Quotient.mk q c)^p, Ideal.Quotient.mk q c) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  change (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c),
    lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c))) = _
  apply Prod.ext
  · exact congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+* K => f c)
      (lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder N p hNp h4N hN hpN q)
  · have h := congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+*
        LPSOriginalRelativeGaussInseparableBranch N hN p q => f c)
      (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder N p hNp h4N hN hpN q)
    change lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c) =
        (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
          (Ideal.Quotient.mk q c) at h
    rw [h]
    exact RingEquiv.apply_symm_apply _ _
lemma lpsOriginalRelativeGaussNormalizationSecondOrder_mem_firstFiberIdeal_iff
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c ∈
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ↔ c ∈ q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  constructor
  · intro hc
    have hc0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    have h := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
      N p hNp h4N hN hpN q c
    rw [hc0, map_zero] at h
    have hz := congrArg Prod.snd h
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz.symm
  · intro hc
    have hc0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    have h := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
      N p hNp h4N hN hpN q c
    rw [hc0, zero_pow (Fact.out : p.Prime).ne_zero] at h
    have he : e (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c)) = e 0 :=
      h.trans (map_zero e).symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp (e.injective he)
def lpsOriginalRelativeGaussNormalizationFirstFiberMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalGaussAffineOrder N hN p ⧸ q) →+*
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) :=
  Ideal.Quotient.lift q ((Ideal.Quotient.mk _).comp (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (fun _c hc => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) hc))
def lpsOriginalRelativeGaussNormalizationSecondFiberMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalGaussAffineOrder N hN p ⧸ q) →+*
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) :=
  Ideal.Quotient.lift q ((Ideal.Quotient.mk _).comp (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))
    (fun c hc => Ideal.Quotient.eq_zero_iff_mem.mpr ((lpsOriginalRelativeGaussNormalizationSecondOrder_mem_firstFiberIdeal_iff N p hNp h4N hN hpN q c).mpr hc))
end
end QEC.Coding.TannerLiftedProduct


