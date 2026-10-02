-- Prove2me | Definitions.Def_Yukon_52b2b488221380926e2e287b
-- name    : Yukon_52b2b488221380926e2e287b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:33:48.727812+00:00
-- url     : https://prove2.me/theorems/438438b8-2795-4380-95ad-1d6d8a42a05f
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeBoundedFactor.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeBoundedFactor.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeBoundedFactor.lean
--
--   yukon-proof-operation:foundation-direct-d579f8c4e45a3ff547c7f42cf31a99caed30fab9d2209900562d57f07120d3d7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZmUyZGIyOTc4MTRmZmQ4OTIxODJmYzliNDYyMTIyYTZlODQ0MTliYjYyOTViYTFhZGMzNjliNzYwYzlkZWJhZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWQ1NzlmOGM0ZTQ1YTNmZjU0N2M3ZjQyY2YzMWE5OWNhZWQzMGZhYjlkMjIwOTkwMDU2MmQ1N2YwNzEyMGQzZDciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81MmIyYjQ4ODIyMTM4MDkyNmUyZTI4N2IiLCJ2IjoyfQ]

import Definitions.Def_Yukon_a9e97b317e346ba3aee2f1b7











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators Pointwise
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RCN180 (encodeBox reconstruct_encodeBox)
open RelativeContactOrder6814 RelativeContactRank6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

def blocksOf {D w L s : ℕ} (m : ℕ) (Q : globalCoefficientBox K D w L s) :
    LocalSource K m L s :=
  fun r => extractBlock K D w L s 0 0 0 r.val (encodeBox Q)

theorem blocksOf_coeff {D w L s : ℕ} (m : ℕ)
    (Q : globalCoefficientBox K D w L s) (r : Fin m) :
    (blocksOf K m Q r).val = (homogenizedTranslation K 0 0 0 Q.val).coeff r.val := by
  rw [← reconstruct_encodeBox Q, translation_reconstruct_coeff]
  rfl

theorem contact_unpack_blocksOf {D w L s : ℕ} (m : ℕ)
    (Q : globalCoefficientBox K D w L s) :
    ContactAtLeast K 0 0 0 m (Q.val-unpack K m L s (blocksOf K m Q)) := by
  rw [contactAtLeast_iff_block_divisibility]
  intro r
  by_cases hr : r < m
  · rw [map_sub, Polynomial.coeff_sub, translated_unpack_coeff K m L s _ ⟨r,hr⟩,
      blocksOf_coeff, sub_self]
    exact dvd_zero _
  · simp [show m-r=0 by omega]

theorem jet_mem_range_of_globalBox {D w L s : ℕ} (m : ℕ)
    (Q : globalCoefficientBox K D w L s) :
    (contactSubmodule K 0 0 0 m).mkQ Q.val ∈ LinearMap.range (boundedJetMap K m L s) := by
  refine ⟨blocksOf K m Q,?_⟩
  change (Submodule.Quotient.mk (unpack K m L s (blocksOf K m Q)) :
      Poly4 K ⧸ contactSubmodule K 0 0 0 m) = Submodule.Quotient.mk Q.val
  symm
  exact (Submodule.Quotient.eq _).mpr (contact_unpack_blocksOf K m Q)

theorem globalBox_mul {D L s D' L' s' : ℕ} {F Q : Poly4 K}
    (hF : F ∈ globalCoefficientBox K D 1 L s)
    (hQ : Q ∈ globalCoefficientBox K D' 1 L' s') :
    F*Q ∈ globalCoefficientBox K (D+D') 1 (L+L') (s+s') := by
  have hset : globalExponents D 1 L s + globalExponents D' 1 L' s' ⊆
      globalExponents (D+D') 1 (L+L') (s+s') := by
    rintro _ ⟨a,ha,b,hb,rfl⟩
    simp only [globalExponents, Set.mem_setOf_eq, Finsupp.add_apply,
      Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at ha hb ⊢
    omega
  change F*Q ∈ MvPolynomial.restrictSupport K _
  apply MvPolynomial.restrictSupport_mono (R:=K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hF hQ

theorem globalBox_mono_total_slope {D L s L' s' : ℕ}
    (hL : L ≤ L') (hs : s ≤ s') :
    globalCoefficientBox K D 1 L s ≤ globalCoefficientBox K D 1 L' s' := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  exact ⟨hd.1.trans hL,hd.2.1.trans hs,hd.2.2⟩

theorem factorJetMap_mem_bounded
    {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF)
    (hT : TF ≤ L) (hR : RF ≤ s)
    (v : LinearMap.range (boundedJetMap K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))) :
    factorJetMap K 0 0 0 m F hF v.val ∈ LinearMap.range (boundedJetMap K m L s) := by
  obtain ⟨q,hq⟩ := v.property
  rw [← hq]
  change (contactSubmodule K 0 0 0 m).mkQ
    (F*unpack K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) q) ∈ _
  apply jet_mem_range_of_globalBox K (D:=DF+(m-contactOrder K 0 0 0 F))
    (w:=1) (L:=L) (s:=s) m
    ⟨F*unpack K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) q,?_⟩
  exact globalBox_mono_total_slope K (L':=L) (s':=s) (by omega) (by omega)
    (globalBox_mul K hbox (unpack_mem K _ _ _ q))

def boundedFactorMap {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :
    LinearMap.range (boundedJetMap K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF)) →ₗ[K]
      LinearMap.range (boundedJetMap K m L s) :=
  LinearMap.codRestrict _
    ((factorJetMap K 0 0 0 m F hF).comp
      (LinearMap.range (boundedJetMap K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))).subtype)
    (factorJetMap_mem_bounded K F hF hbox hT hR)

theorem boundedFactorMap_injective {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :
    Function.Injective (boundedFactorMap K (m:=m) F hF hbox hT hR) := by
  intro a b hab
  apply Subtype.ext
  apply factorJetMap_injective K 0 0 0 m F hF
  exact congrArg Subtype.val hab

abbrev RelativeJetTarget {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :=
  LinearMap.range (boundedJetMap K m L s) ⧸
    LinearMap.range (boundedFactorMap K (m:=m) F hF hbox hT hR)

/-- Exact bounded relative dimension: this is the subtraction appearing in
the saved arithmetic certificates, with no extra rank hypothesis. -/
theorem relativeJetTarget_finrank {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s) :
    Module.finrank K (RelativeJetTarget K (m:=m) F hF hbox hT hR) =
      localRankBound m L s -
        localRankBound (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) := by
  have hi := LinearMap.finrank_range_of_inj
    (boundedFactorMap_injective K (m:=m) F hF hbox hT hR)
  rw [boundedJetMap_finrank] at hi
  have hq := (LinearMap.range
    (boundedFactorMap K (m:=m) F hF hbox hT hR)).finrank_quotient_add_finrank
  rw [hi, boundedJetMap_finrank] at hq
  change Module.finrank K (RelativeJetTarget K (m:=m) F hF hbox hT hR) + _ = _ at hq
  omega

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


