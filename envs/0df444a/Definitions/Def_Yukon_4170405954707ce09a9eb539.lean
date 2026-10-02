-- Prove2me | Definitions.Def_Yukon_4170405954707ce09a9eb539
-- name    : Yukon_4170405954707ce09a9eb539
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T02:47:26.599487+00:00
-- url     : https://prove2.me/theorems/ae53f512-18eb-41ed-9c78-31669597aa56
-- title:
--   LowerFoundation source section 7
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-direct-dependency-Yukon_4170405954707ce09a9eb539
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOWJiYmUyM2E3NjhjYzExMWY5ZWVlNDI5ZjU0NWRiMjFhZTQ3NGEwZjVhNzE1YzU5ZTQyMjIyNjU1OGZmODRjNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tZGlyZWN0LWRlcGVuZGVuY3ktWXVrb25fNDE3MDQwNTk1NDcwN2NlMDlhOWViNTM5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNDE3MDQwNTk1NDcwN2NlMDlhOWViNTM5IiwidiI6Mn0]

import Definitions.Def_Yukon_28e0be7dc74857fb9ba06094
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.FM. -/
section PackedLegacy_FM
namespace ProximityPrize.SubmissionLower.RCN230
open IsLocalRing Polynomial Ideal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable (R:Type*) [CommRing R]
theorem exists_monic_span_compat {k:Type*} [Field k]
   (I:Ideal k[X]) (hne:I≠⊥):
   ∃ f,f.Monic∧I=Ideal.span {f}:=by
 classical
 letI:DecidableEq k:=Classical.decEq k
 obtain ⟨x,h,spanx⟩:=Ideal.exists_normalized_span_of_isPrincipal I
 refine ⟨x,(Polynomial.normalize_eq_self_iff_monic ?_).mp h,spanx⟩
 by_contra eq0
 simp [eq0,spanx] at hne
theorem exists_monic_span_sup_map_eq_compat
   (p:Ideal R[X]) (hmax:(p.comap Polynomial.C).IsMaximal)
   (hne:p≠(p.comap Polynomial.C).map Polynomial.C):
   ∃ f:R[X],f.Monic∧
     p=(p.comap Polynomial.C).map Polynomial.C ⊔ Ideal.span {f}:=by
 let q:=p.comap Polynomial.C
 letI:Field (R ⧸ q):=Ideal.Quotient.field q
 have hne':Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk q)) p≠⊥:=by
   simp only [ne_eq,Ideal.map_eq_bot_iff_le_ker,
     Polynomial.ker_mapRingHom,q,Ideal.mk_ker]
   exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le hne.symm)
 rcases exists_monic_span_compat
     (Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk q)) p) hne' with
   ⟨y,mony,hy⟩
 have hyLift:y∈Polynomial.lifts (Ideal.Quotient.mk q):=
   Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _
 rcases Polynomial.lifts_and_natDegree_eq_and_monic hyLift mony with
   ⟨f,hf,_deg,monf⟩
 refine ⟨f,monf,?_⟩
 trans Ideal.comap (Polynomial.mapRingHom (Ideal.Quotient.mk q))
   ((Ideal.span {f}).map (Polynomial.mapRingHom (Ideal.Quotient.mk q)))
 · rw [Ideal.map_span,Polynomial.coe_mapRingHom,Set.image_singleton,hf, ←hy,
     Ideal.comap_map_of_surjective' _
       (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)]
   simpa [Polynomial.ker_mapRingHom,q] using Ideal.map_comap_le
 · rw [Ideal.comap_map_of_surjective' _
     (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective),
     sup_comm,Polynomial.ker_mapRingHom,Ideal.mk_ker]
theorem height_map_C_compat [IsNoetherianRing R]
   (p:Ideal R) [p.IsMaximal]:
   (p.map Polynomial.C).height=p.height:=by
 have:(p.map Polynomial.C).LiesOver p:=
   ⟨Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' Ideal.le_comap_map⟩
 simp [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p]
theorem polynomial_localization_isRegularLocalRing_compat
   [IsRegularLocalRing R] (p:Ideal R[X]) [p.IsPrime]
   (hcomap:p.comap Polynomial.C=maximalIdeal R):
   IsRegularLocalRing (Localization.AtPrime p):=by
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 let q:=(maximalIdeal R).map Polynomial.C
 have qle:q ≤ p:=by simpa [q, ←hcomap] using Ideal.map_comap_le
 have hreg:=(isRegularLocalRing_iff R).mp (inferInstance:IsRegularLocalRing R)
 have hfg':=(maximalIdeal R).fg_of_isNoetherianRing
 have hfg:=Submodule.FG.finite_generators hfg'
 have ht:(maximalIdeal R).height ≤ q.height:=
   le_of_eq (height_map_C_compat R (maximalIdeal R)).symm
 by_cases heq:p=q
 · have ht1:(maximalIdeal R).height ≤ p.height:=by simpa [heq]
   have hspan:Ideal.span
       ((algebraMap R (Localization.AtPrime p)) ''
         (maximalIdeal R).generators)=maximalIdeal (Localization.AtPrime p):=by
     rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p),
       RingHom.coe_comp,Set.image_comp, ←Ideal.map_span, ←Ideal.map_span]
     simp only [Ideal.span,(maximalIdeal R).span_generators,algebraMap_eq,
       q, ←heq,Localization.AtPrime.map_eq_maximalIdeal]
   simp only [←maximalIdeal_height_eq_ringKrullDim,
     ←IsLocalization.height_under p.primeCompl,
     IsLocalization.AtPrime.under_maximalIdeal _ p,ge_iff_le]
   apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
   simp only [maximalIdeal_height_eq_ringKrullDim, ←hreg,Nat.cast_le,
     ←hspan, ←Submodule.FG.generators_ncard hfg']
   exact (Submodule.spanFinrank_span_le_ncard_of_finite (hfg.image _)).trans
     (Set.ncard_image_le hfg)
 · have hlt:q < p:=lt_of_le_of_ne qle (Ne.symm heq)
   have hpmax:(p.comap Polynomial.C).IsMaximal:=by
     simpa [hcomap] using maximalIdeal.isMaximal R
   obtain ⟨y,_,hy⟩:=
     exists_monic_span_sup_map_eq_compat R p hpmax (by simpa [hcomap])
   have peq:p=Ideal.span
       (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}):=by
     simp only [Set.union_comm,Ideal.span_union, ←Ideal.map_span,
       algebraMap_eq,sup_comm]
     nth_rw 1 [hy,hcomap, ←(maximalIdeal R).span_generators]
   simp only [←Localization.AtPrime.map_eq_maximalIdeal,peq,Ideal.map_span]
   rw [←maximalIdeal_height_eq_ringKrullDim,
     ←IsLocalization.height_under p.primeCompl,
     IsLocalization.AtPrime.under_maximalIdeal _ p]
   apply le_trans _
     (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime hlt))
   apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
   rw [WithBot.coe_add,maximalIdeal_height_eq_ringKrullDim,WithBot.coe_one,
     ←hreg, ←Nat.cast_one, ←Nat.cast_add,Nat.cast_le]
   have hfin:=(hfg.image (algebraMap R R[X])).union (Set.finite_singleton y)
   apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (hfin.image _))
   apply le_trans (Set.ncard_image_le hfin) (le_trans (Set.ncard_union_le _ _) _)
   rw [Set.ncard_singleton,add_le_add_iff_right,
     ←Submodule.FG.generators_ncard hfg']
   exact Set.ncard_image_le hfg
instance polynomial_isRegularRing_compat [IsRegularRing R]:
   IsRegularRing R[X]:=by
 apply isRegularRing_iff.mpr
 intro p hp
 let q:=p.comap Polynomial.C
 let S:=(Localization.AtPrime q)[X]
 let pc:=Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
 letI:Algebra R[X] S:=Polynomial.algebra R (Localization.AtPrime q)
 haveI:IsLocalization pc S:=Polynomial.isLocalization _ _
 let pS:=p.map (algebraMap R[X] S)
 have hdisj:Disjoint (pc:Set R[X]) (p:Set R[X]):=by
   apply Set.disjoint_left.mpr
   rintro _ ⟨b,hb,rfl⟩ hp
   exact hb hp
 haveI:pS.IsPrime:=
   IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance hdisj
 haveI:IsLocalization.AtPrime (Localization.AtPrime pS) p:=by
   convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
     pc (Localization.AtPrime pS) pS
   exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance hdisj).symm
 haveI:IsRegularLocalRing (Localization.AtPrime q):=
   IsRegularRing.isRegularLocalRing_localization q
 have hbase:pS.comap Polynomial.C=maximalIdeal (Localization.AtPrime q):=by
   rw [←IsLocalization.map_under q.primeCompl _ (pS.comap Polynomial.C),
     ←IsLocalization.map_under q.primeCompl _
       (maximalIdeal (Localization.AtPrime q))]
   simp only [Ideal.comap_comap,S,pS]
   rw [←Polynomial.algebraMap_eq (R:=Localization.AtPrime q),
     ←IsScalarTower.algebraMap_eq R (Localization.AtPrime q)
       (Localization.AtPrime q)[X],
     IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X],
     ←Ideal.comap_comap, ←Ideal.under_def R[X],
     IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance hdisj]
   simp [q,IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
 haveI:=polynomial_localization_isRegularLocalRing_compat
   (Localization.AtPrime q) pS hbase
 exact IsRegularLocalRing.of_ringEquiv (R:=Localization.AtPrime pS)
   (IsLocalization.algEquiv p.primeCompl
     (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
instance mvPolynomial_isRegularRing_compat [IsRegularRing R]
   {ι:Type*} [Finite ι]:IsRegularRing (MvPolynomial ι R):=by
 induction ι using Finite.induction_empty_option with
 | of_equiv e H =>
     exact IsRegularRing.of_ringEquiv (MvPolynomial.renameEquiv _ e).toRingEquiv
 | h_empty =>
     exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv R _).symm
 | h_option IH =>
     exact IsRegularRing.of_ringEquiv
       (MvPolynomial.optionEquivLeft _ _).toRingEquiv.symm
theorem mvPolynomial_atPrime_isRegularLocalRing
   {K:Type*} [Field K] {ι:Type*} [Finite ι]
   (p:Ideal (MvPolynomial ι K)) [p.IsPrime]:
   IsRegularLocalRing (Localization.AtPrime p):=by
 letI:IsRegularRing K:=inferInstance
 letI:IsRegularRing (MvPolynomial ι K):=
   mvPolynomial_isRegularRing_compat K
 infer_instance
end
end ProximityPrize.SubmissionLower.RCN230
end PackedLegacy_FM
end Compact_PackedLegacy


