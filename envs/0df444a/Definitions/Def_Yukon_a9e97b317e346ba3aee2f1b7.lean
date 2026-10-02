-- Prove2me | Definitions.Def_Yukon_a9e97b317e346ba3aee2f1b7
-- name    : Yukon_a9e97b317e346ba3aee2f1b7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:15:54.562377+00:00
-- url     : https://prove2.me/theorems/ca5d6bec-6b04-4640-a776-885591540d17
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeBoundedRealization.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeBoundedRealization.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeBoundedRealization.lean
--
--   yukon-proof-operation:foundation-direct-51a3a3eba461494b5f6ed2c847373d59ce18c3cbb271396558e5daaf238fa530
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiN2ZkM2UwNmQ2NTgyOGI0MDMwZTgzZTE2NzUzZmE1YWZkNGUzMDZhNmFiOWM2NzdlMzQ2NzdmYjlhZWE5OTZjNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTUxYTNhM2ViYTQ2MTQ5NGI1ZjZlZDJjODQ3MzczZDU5Y2UxOGMzY2JiMjcxMzk2NTU4ZTVkYWFmMjM4ZmE1MzAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hOWU5N2IzMTdlMzQ2YmEzYWVlMmYxYjciLCJ2IjoyfQ]

import Definitions.Def_Yukon_9aee69d722b041638a1f477d

import Definitions.Def_Yukon_5eeadd6de4425031552f4a01










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814 RelativeContactRank6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

def unpackExponent (r : ℕ) (d : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.cons (r-d 0) d

theorem monomial3_eq (d : Fin 3 →₀ ℕ) (a : K) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 *
        MvPolynomial.X 1 ^ d 1 * MvPolynomial.X 2 ^ d 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem translated_unpack_monomial (r : ℕ) (d : Fin 3 →₀ ℕ) (a : K)
    (hd : d 0 ≤ r) :
    homogenizedTranslation K 0 0 0 (MvPolynomial.monomial (unpackExponent r d) a) =
      Polynomial.monomial r (MvPolynomial.monomial d a) := by
  rw [RCN122.monomial_eq K, monomial3_eq K,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow]
  simp [unpackExponent, homogenizedTranslation, translationVariables, seedAffine,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, mul_pow]
  simp only [show (Finsupp.cons (r-d 0) d) (1 : Fin 4) = d 0 from rfl,
    show (Finsupp.cons (r-d 0) d) (2 : Fin 4) = d 1 from rfl,
    show (Finsupp.cons (r-d 0) d) (3 : Fin 4) = d 2 from rfl]
  conv_rhs => rw [show r = (r-d 0)+d 0 by omega, pow_add]
  ring

def unpackBlock (r : ℕ) : RCN119.Poly K →ₗ[K] Poly4 K :=
  (MvPolynomial.basisMonomials (Fin 3) K).constr K
    (fun d => MvPolynomial.monomial (unpackExponent r d) 1)

theorem unpackBlock_apply (r : ℕ) (p : RCN119.Poly K) :
    unpackBlock K r p = ∑ d ∈ p.support,
      p.coeff d • MvPolynomial.monomial (unpackExponent r d) (1 : K) := by
  rw [unpackBlock, Module.Basis.constr_apply]
  rfl

theorem translated_unpackBlock (r : ℕ) (p : RCN119.Poly K)
    (hp : p.degreeOf 0 ≤ r) :
    homogenizedTranslation K 0 0 0 (unpackBlock K r p) = Polynomial.monomial r p := by
  classical
  rw [unpackBlock_apply, map_sum]
  have he : ∀ d ∈ p.support,
      homogenizedTranslation K 0 0 0
          (p.coeff d • MvPolynomial.monomial (unpackExponent r d) (1 : K)) =
        Polynomial.monomial r (MvPolynomial.monomial d (p.coeff d)) := by
    intro d hd
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact translated_unpack_monomial K r d (p.coeff d)
      (MvPolynomial.degreeOf_le_iff.mp hp d hd)
  rw [Finset.sum_congr rfl he]
  conv_rhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum]

theorem unpackBlock_mem (m L s : ℕ) (r : Fin m)
    (p : coefficientBox K (min r.val L) L s) :
    unpackBlock K r.val p.val ∈ globalCoefficientBox K m 1 L s := by
  classical
  rw [unpackBlock_apply]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
  left
  have hb := p.property hd
  change d 0 ≤ min r.val L ∧ d 0+d 1+d 2 ≤ L ∧ d 1 ≤ s at hb
  change d 0+d 1+d 2 ≤ L ∧ d 1 ≤ s ∧ (r.val-d 0)+1*d 0+(1-1)*d 1 < m
  have hr := r.isLt
  omega

abbrev LocalSource (m L s : ℕ) :=
  (r : Fin m) → coefficientBox K (min r.val L) L s

def unpack (m L s : ℕ) : LocalSource K m L s →ₗ[K] Poly4 K where
  toFun p := ∑ r : Fin m, unpackBlock K r.val (p r).val
  map_add' p q := by simp [map_add, Finset.sum_add_distrib]
  map_smul' a p := by simp [map_smul, Finset.smul_sum]

theorem unpack_mem (m L s : ℕ) (p : LocalSource K m L s) :
    unpack K m L s p ∈ globalCoefficientBox K m 1 L s := by
  change (∑ r : Fin m, unpackBlock K r.val (p r).val) ∈ _
  apply Submodule.sum_mem
  intro r _
  exact unpackBlock_mem K m L s r (p r)

theorem translated_unpack (m L s : ℕ) (p : LocalSource K m L s) :
    homogenizedTranslation K 0 0 0 (unpack K m L s p) =
      ∑ r : Fin m, Polynomial.monomial r.val (p r).val := by
  change homogenizedTranslation K 0 0 0 (∑ r : Fin m, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply translated_unpackBlock
  exact ((coefficientBox_bounds K _ _ _ _).mp (p r).property).1.trans (min_le_left _ _)

theorem translated_unpack_coeff (m L s : ℕ) (p : LocalSource K m L s) (r : Fin m) :
    (homogenizedTranslation K 0 0 0 (unpack K m L s p)).coeff r.val = (p r).val := by
  classical
  rw [translated_unpack, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Fin.val_inj]
  simp

def sourceJet (m L s : ℕ) : LocalSource K m L s →ₗ[K] LocalTarget K m L s :=
  LinearMap.pi fun r =>
    (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp (LinearMap.proj r)

theorem sourceJet_surjective (m L s : ℕ) :
    Function.Surjective (sourceJet K m L s) := by
  classical
  intro v
  choose p hp using fun r => (v r).property
  refine ⟨p,?_⟩
  funext r
  apply Subtype.ext
  exact hp r

theorem sourceJet_eq_zero_iff (m L s : ℕ) (p : LocalSource K m L s) :
    sourceJet K m L s p = 0 ↔ ContactAtLeast K 0 0 0 m (unpack K m L s p) := by
  rw [contactAtLeast_iff_block_divisibility]
  constructor
  · intro h n
    by_cases hn : n < m
    · have hr := congrArg (fun v : LocalTarget K m L s => (v ⟨n,hn⟩).val) h
      have hz : contactJet K (m-n) (p ⟨n,hn⟩).val = 0 := hr
      rw [translated_unpack_coeff K m L s p ⟨n,hn⟩]
      exact (contactJet_eq_zero_iff K (m-n) _).mp hz
    · simp [show m-n=0 by omega]
  · intro h
    funext r
    apply Subtype.ext
    change contactJet K (m-r.val) (p r).val = 0
    apply (contactJet_eq_zero_iff K (m-r.val) _).mpr
    have hr := h r.val
    rw [translated_unpack_coeff] at hr
    exact hr

def boundedJetMap (m L s : ℕ) : LocalSource K m L s →ₗ[K]
    (Poly4 K ⧸ contactSubmodule K 0 0 0 m) :=
  (contactSubmodule K 0 0 0 m).mkQ.comp (unpack K m L s)

theorem boundedJetMap_ker (m L s : ℕ) :
    LinearMap.ker (boundedJetMap K m L s) = LinearMap.ker (sourceJet K m L s) := by
  ext p
  simp only [LinearMap.mem_ker]
  change ((contactSubmodule K 0 0 0 m).mkQ (unpack K m L s p) = 0) ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_contactSubmodule,
    ← sourceJet_eq_zero_iff]

/-- The bounded space has the exact dimension used by the numeric certificates,
now as an image in the actual contact-jet quotient. -/
theorem boundedJetMap_finrank (m L s : ℕ) :
    Module.finrank K (LinearMap.range (boundedJetMap K m L s)) = localRankBound m L s := by
  have hfull := LinearMap.range_eq_top.mpr (sourceJet_surjective K m L s)
  have hs := (sourceJet K m L s).finrank_range_add_finrank_ker
  rw [hfull, finrank_top, localTarget_finrank_eq] at hs
  have hb := (boundedJetMap K m L s).finrank_range_add_finrank_ker
  rw [boundedJetMap_ker] at hb
  omega

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


