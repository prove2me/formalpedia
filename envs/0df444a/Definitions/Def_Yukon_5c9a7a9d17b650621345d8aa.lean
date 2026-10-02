-- Prove2me | Definitions.Def_Yukon_5c9a7a9d17b650621345d8aa
-- name    : Yukon_5c9a7a9d17b650621345d8aa
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:27:09.332955+00:00
-- url     : https://prove2.me/theorems/89b8bb73-1aa8-426c-99f1-646fb987b911
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailReduced.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailReduced.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailReduced.lean
--
--   yukon-proof-operation:foundation-direct-3f698328c16aea2029975aacc6fb2b0306421f7612d65e1afb48c2005a32c7e9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMjVhOGZlYWI4NTgxNTM4ZWI4MTk0ZDJmODVmMGE1ODYyY2EwNDRlMmMzNjI1OWNmMjVjZDM2ZDk1YjRhNGY4YyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTNmNjk4MzI4YzE2YWVhMjAyOTk3NWFhY2M2ZmIyYjAzMDY0MjFmNzYxMmQ2NWUxYWZiNDhjMjAwNWEzMmM3ZTkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81YzlhN2E5ZDE3YjY1MDYyMTM0NWQ4YWEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_28be9ec982818aa5b286d017












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailReduced
open scoped Classical BigOperators
open RCN332 BoundaryTailProjection
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.BoundaryTailReduced.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.BoundaryTailReduced.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem exists_reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   Nonempty (ReducedActiveGeometry S):=by
 obtain ⟨base, hactive, hZ, -⟩ :=
   BoundaryTailProjection.exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 obtain ⟨D, hlam, hmu⟩:=RCN038.exists_adaptiveNestedProjectionDataActive_in base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) (Set.range (polynomialEmbedding K))
   (Set.infinite_range_of_injective (polynomialEmbedding_injective K))
 exact ⟨⟨base, hactive, hZ, D, hlam, hmu⟩⟩
noncomputable def reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
noncomputable def reducedUnitFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :=
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 activeNestedUnitFamily A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
noncomputable def reducedBudgetFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
noncomputable def reducedBaseOrd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p)
   (C:FirstTailComponent S):SeparableLiteralCoordinate C.1:=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 exact (reducedActiveGeometry S hfirstProper hflagChar hmixed).base C'
theorem reducedBudgetFamily_yzPositive
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p)
   (C:FirstTailComponent S) :
   1 ≤ (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C:=by
 let hd:=ordinary_sub_reducedFirstCut_dvd S
 let C':=regularComponentEquiv hd C
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 let U:=reducedUnitFamily S hfirstProper hflagChar hmixed
 change 1 ≤ U.toPrimeFlagBudgetFamily.yzCost C'
 change 1 ≤ coordinateDegree (GenericField K)
   (CoordinateField (GenericField K) C'.1) (U.yzProjection C')
 apply one_le_coordinateDegree_of_transcendental_value
 have hproj:U.yzProjection C' = coordinateOfGate
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C'):=rfl
 rw [hproj, coordinateOfGate_value]
 exact A.data.uTranscendental C'
theorem reducedBudgetFamily_yzPole
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p)
   (C:FirstTailComponent S) :
   LiteralSupportPoleBound
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C):=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 have heq:regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S) C = C':=by
   apply Subtype.ext
   rfl
 rw [show (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C =
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C' by
   simp only [reducedBudgetFamily, PrimeFlagBudgetFamily.ofCongruentCut, heq]]
 change LiteralSupportPoleBound
   ((reducedActiveGeometry S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C')
 exact (reducedUnitFamily S hfirstProper hflagChar hmixed).toAdaptiveUnitPoleBudget.yzPole C'
theorem reducedFixedPowersGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStageGeneral S)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicityGeneral S hfirstProper))
   (reducedFixedPowersGeneral S hfirstProper hflagChar hmixed)
theorem transportedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.BoundaryTailReduced


