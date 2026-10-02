-- Prove2me | Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
-- name    : Yukon_755f5ab5e1dfa660f8e11f09
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T04:28:50.353913+00:00
-- url     : https://prove2.me/theorems/96fdca7a-f2f6-4cc6-9762-63501673d153
-- title:
--   LowerFoundation source part 5/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:foundation-direct-f8db70f9534f6a1c49104b47523f0411888733d4a81b8b135068025e428b0f4d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOGU2NDdiMWQ2NDlkZDgzNTJhODBkZDUzM2U5NmZmNDQzZjVjOTI4ZWRjY2ZhZDc5MGIyOGViMmY5M2ZhZDJiNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWY4ZGI3MGY5NTM0ZjZhMWM0OTEwNGI0NzUyM2YwNDExODg4NzMzZDRhODFiOGIxMzUwNjgwMjVlNDI4YjBmNGQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83NTVmNWFiNWUxZGZhNjYwZjhlMTFmMDkiLCJ2IjoyfQ]

import Definitions.Def_Yukon_7fa2e9b1f92d4b5807689791






















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.P9. -/
section PackedLegacy_P9
namespace ProximityPrize.SubmissionLower.RCN332
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN332.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN332.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
def reducedFirstCut
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):MvPolynomial (Fin 3) (GenericField K) :=
 reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1)
theorem ordinary_sub_reducedFirstCut_dvd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
     reducedFirstCut S :=
 S.G_dvd_surface.trans
   (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) (support a b s)
     S.F (w + 1))
theorem reducedFirstCut_proper
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ¬ S.G ∣ reducedFirstCut S:=by
 intro hr
 apply hfirstProper
 have h:=(ordinary_sub_reducedFirstCut_dvd S).add hr
 simpa only [reducedFirstCut, sub_add_cancel] using h
theorem reducedFirstCut_in_flag
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   PolynomialInFlag (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S):=by
 exact reducedGlobalTailCut_in_flag (polynomialEmbedding K) (support a b s)
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩ (w + 1)
noncomputable def reducedUnitFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
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
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
noncomputable def reducedBaseOrd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
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
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
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
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
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
noncomputable def reducedMultiplicityGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
theorem reducedFixedPowersGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
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
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
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
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.RCN332
end PackedLegacy_P9

/-! Packed from ProximityPrize.SubmissionLower.Q2. -/
section PackedLegacy_Q2
namespace ProximityPrize.SubmissionLower.RCN335
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN335.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN335.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem exists_delayedTailMultiplicityProvider_of_reducedGeneral
   {a b s:ℕ}
   (agreementCap:ℕ)
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card = agreementCap + stageErrorCap)
   (hagreement:∀ gamma ∈ Gamma, agreementCap ≤ (S.agreementFiber gamma).card)
   (hwa:w < agreementCap)
   (hshort:w + 1 ≤ bound) (hchar:bound < p)
   (hbox:S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate:stageErrorCap + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2:=reducedResidualAgreementFlag (support a b s) (w + 2)) S):=by
 classical
 let supp:=support a b s
 let S0:=loosenStageGeneral S
 let T:=globalTailCut (polynomialEmbedding K) S.F (w + 1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let secondFlag:=reducedResidualAgreementFlag supp (w + 2)
 let B:=reducedBudgetFamily S hfirstProper hflagChar hmixed
 let multiplicity:=reducedMultiplicityGeneral S hfirstProper
 have hone:∀ C, 1 ≤ multiplicity C:=by
   exact loosenStageGeneral_one_le_localMultiplicity S hfirstProper
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) :
     (componentSeeds (GenericField K) S.G T H Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     agreementCap bound seedCap slopeCap hnodes hagreement
     hwa (by norm_num [w])
     hshort hchar hbox B
     (reducedBudgetFamily_yzPositive S hfirstProper hflagChar hmixed C)
     hall (reducedBudgetFamily_yzPole S hfirstProper hflagChar hmixed C)
 have branchBound (C:FirstTailComponent S) :
     ((∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
         globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1 ∧
         (componentSeeds (GenericField K) S.G T H Gamma
           (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
             multiplicity C * B.weightedCost secondFlag C) ∨
       (∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1)):=by
   have dichotomy:=local_order_tail_dichotomy S0
     (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
   rcases dichotomy.2 with hproper | htangent
   · left
     obtain ⟨delay, hdelay, hdelayMu, htail⟩:=hproper
     have hzero:∀ gamma ∈ componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C,
         MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
           (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0:=by
       intro gamma hgamma
       have hGamma:=componentSeeds_subset (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
       exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected
         gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
         (S.solution gamma hGamma) (by omega)
     have hcount:=component_secondTail_card_le_mod B C Gamma
       (selectedPoint (polynomialEmbedding K) S.selected)
       (selectedPoint_injective (polynomialEmbedding K) S.selected)
       (laterTail_in_reduced_delay_secondFlag S C delay hdelay) htail hzero
     have hscale:B.weightedCost (delay • secondFlag) C =
         delay * B.weightedCost secondFlag C:=by
       simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
         nsmul_all]
       ring
     rw [hscale] at hcount
     exact ⟨delay, hdelay, hdelayMu, htail,
       hcount.trans (Nat.mul_le_mul_right (B.weightedCost secondFlag C) hdelayMu)⟩
   · exact Or.inr htangent
 have providerDichotomy :=
   loosenStageGeneral_dichotomy_with_tangent S hfirstProper B tangentCount
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=fun C => multiplicity C * B.weightedCost secondFlag C
   one_le_multiplicity:=hone
   tangentYZGate:=htangentGate
   cost_le:=fun _ => le_rfl
   divisor_le :=
     (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixed).divisor_le
       B multiplicity
   componentBound:=?_
   dichotomy:=providerDichotomy }⟩
 intro C
 rcases branchBound C with hproper | htangent
 · obtain ⟨_delay, _hdelay, _hdelayMu, _htail, hcount⟩:=hproper
   exact hcount
 · calc
     (componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=tangentCount C htangent
     _ ≤ B.weightedCost secondFlag C :=
       yzCost_mul_le_weightedCost B secondFlag C (stageErrorCap + 1) htangentGate
     _ = 1 * B.weightedCost secondFlag C:=by simp
     _ ≤ multiplicity C * B.weightedCost secondFlag C :=
       Nat.mul_le_mul_right (B.weightedCost secondFlag C) (hone C)
end
end ProximityPrize.SubmissionLower.RCN335
end PackedLegacy_Q2

/-! Packed from ProximityPrize.SubmissionLower.J4. -/
section PackedLegacy_J4
namespace ProximityPrize.SubmissionLower.RCN087
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 25000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e:ℕ} [CharP Ω p]
local instance _root_.ProximityPrize.SubmissionLower.RCN087.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN087.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
local instance _root_.ProximityPrize.SubmissionLower.RCN087.instDecidableEq_proximityPrize_2 :DecidableEq I:=Classical.decEq I
def IdentityCurveCountProvider
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support) (identityDegree:ℕ):Prop:=
 ∀ i∈S.nodes,
   let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
   (hproper:¬S.G∣T) →
   let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
   ∃ cost:RegularComponent Ω S.G T (regularitySurface φ S.F)→ℕ,
     (∀ C,(componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
       (selectedPoint φ S.selected) C).card≤(e+1)*cost C)∧
     (∑ C,cost C) ≤ identityDegree
public theorem proper_node_fiber_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (identityDegree:ℕ) (hprovider:IdentityCurveCountProvider S identityDegree)
   (i:I) (hi:i∈S.nodes)
   (hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)):
   (Γ.filter (fun γ=>S.Agrees γ i)).card≤(e+1)*identityDegree:=by
 let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨cost,hcomponent,hsum⟩:=hprovider i hi hproper
 have hsub:Gi⊆Γ:=Finset.filter_subset _ _
 have hGpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) S.G=0:=by
   intro γ hγ;exact S.on_component γ (hsub hγ)
 have hTpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) T=0:=by
   intro γ hγ
   exact (selected_agreement_zero_iff φ S.F S.selected p w S.characteristic_bound γ
     (S.degree_le γ (hsub hγ)) (S.solution γ (hsub hγ))
     (S.regular γ (hsub hγ)) (x i) (S.u0 i) (S.u1 i)).mpr
     (Finset.mem_filter.mp hγ).2
 have hHp:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ)
     (regularitySurface φ S.F)≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ S.selected γ)
     (surfaceMap φ (MvPolynomial.pderiv 2 S.F))≠0
   rw [selectedPoint_evaluation]
   exact S.regular γ (hsub hγ)
 calc
   Gi.card≤∑ C:RegularComponent Ω S.G T (regularitySurface φ S.F),
       (componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
         (selectedPoint φ S.selected) C).card:=
     card_le_sum_componentSeeds Ω _ _ _ Gi _ hGpoint hTpoint hHp
   _≤∑ C,(e+1)*cost C:=Finset.sum_le_sum fun C _=>hcomponent C
   _=(e+1)*(∑ C,cost C):=by rw [Finset.mul_sum]
   _≤(e+1)*identityDegree:=Nat.mul_le_mul_left _ hsum
theorem identity_surface_seed_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (a identityDegree:ℕ)
   (hprovider:IdentityCurveCountProvider S identityDegree)
   (hagreement:∀ γ∈Γ,a≤(S.agreementFiber γ).card)
   (hwa:w < a) (han:a ≤ S.nodes.card) (hdegreePos:1 ≤ identityDegree):
   Γ.card*(a-w)≤(S.nodes.card-w)*(e+1)*identityDegree:=by
 classical
 letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
 let relation:K→I→Prop:=fun γ i=>S.Agrees γ i
 let identities:=S.identities
 by_cases hI:identities.card ≤ w
 · have hfiber:∀ i∈S.nodes\identities,
       (Γ.filter (fun γ=>relation γ i)).card≤(e+1)*identityDegree:=by
     intro i hi
     obtain ⟨hiNode,hiNot⟩:=Finset.mem_sdiff.mp hi
     have hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i):=by
       intro hd
       exact hiNot (Finset.mem_filter.mpr ⟨hiNode,Ideal.mem_span_singleton.mpr hd⟩)
     exact proper_node_fiber_bound S identityDegree hprovider i hiNode hproper
   simpa only [mul_assoc] using RCN173.sharp_incidence_bound relation Γ S.nodes
     identities a w ((e+1)*identityDegree)
     (identityNodes_subset φ S.componentIdeal S.F S.nodes x S.u0 S.u1 w)
     hI hwa han hagreement hfiber
 · have hi:w < identities.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈identities→
       (S.selected t.1).eval (x i)=S.u0 i+t.1*S.u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ S.componentIdeal S.F S.nodes x S.u0 S.u1
       p w S.characteristic_bound (S.selected t.1) t.1 (S.degree_le t.1 t.2)
       (S.solution t.1 t.2) (S.regular t.1 t.2) (S.selected_point_ideal t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
     φ S.componentIdeal S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
     S.nodes x S.u0 S.u1 w S.x_injective hi
     (fun t:{γ:K//γ∈Γ}=>t.1) (fun t=>S.selected t.1)
     (fun t=>S.degree_le t.1 t.2) hvalues
   have hsmall:Γ.card ≤ e+1:=by
     have hf:Γ.filter (fun γ=>S.selected γ=P0+Polynomial.C γ*P1)=Γ:=
       Finset.filter_eq_self.mpr (fun γ hγ=>hpencil ⟨γ,hγ⟩)
     simpa only [hf] using S.no_large_pencil P0 P1 h0 h1
   calc
     Γ.card*(a-w)≤(e+1)*(a-w):=Nat.mul_le_mul_right _ hsmall
     _≤(e+1)*(S.nodes.card-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _≤(S.nodes.card-w)*(e+1)*identityDegree:=by
       have h:=Nat.mul_le_mul_left ((S.nodes.card-w)*(e+1)) hdegreePos
       simpa [mul_assoc,mul_comm,mul_left_comm] using h
end
end ProximityPrize.SubmissionLower.RCN087
end PackedLegacy_J4

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier23 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DU. -/
section PackedLegacy_DU
namespace ProximityPrize.SubmissionLower.RCN049
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN274 RCN198
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem exists_agreement_projection_of_caps
   (S:ResidualStage φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   ∃ base:∀ C:RegularComponent Ω S.G
       (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=agreementPolynomial φ S.F w x0 u0 u1
 let H:=regularitySurface φ S.F
 have hsy:s+2 < b+s+3:=by omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag (support a b s) w) T:=
   surfaceMap_agreement_in_sharp_flag hsy (phi:=φ)
     ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
     w (fun j:ℕ => (j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hTY':T.degreeOf 0 ≤ 1+w*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact sharpResidualAgreementFlag_ys (support a b s) hsy w
 have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*w:=by
   apply hTS.trans_eq
   simp only [sharpResidualAgreementFlag,sharpAgreementDirection,
     RCN198.support]
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:coordinateMixedDegree Ω S.G T 2<p:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Ω S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C => regularComponent_exists_separableLiteralCoordinate6630
     φ S.F S.G T p S.G_dvd_surface S.irreducible_G hproper
     S.y_dependent hGdegree hmixZ C
 let base:∀ C:RegularComponent Ω S.G T H,
     SeparableLiteralCoordinate C.1:=fun C => (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Ω S.G T H,
     D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Ω S.G T H,LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Ω C.1 2 htr
     p S.G T S.irreducible_G
     (regularComponent_G_mem Ω S.G T H C)
     (regularComponent_T_mem Ω S.G T H C)
     hproper hGdegree hmixZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end ProximityPrize.SubmissionLower.RCN049
end PackedLegacy_DU

/-! Packed from ProximityPrize.SubmissionLower.EQ. -/
section PackedLegacy_EQ
namespace ProximityPrize.SubmissionLower.RCN146
open scoped Classical BigOperators
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN146.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN146.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
def identityCurveDegree (flag:FlagDegree) (a b s w:ℕ):ℕ:=
 flagMixed flag (paddedCut a b s (w+1)) unitZFlag+
   flagMixed flag (paddedCut a b s (w+1)) unitYZFlag
theorem mixed_padded_le_succ (flag:FlagDegree) (a b s d:ℕ) (r:FlagDegree):
   flagMixed flag (paddedCut a b s d) r ≤
     flagMixed flag (paddedCut a b s (d+1)) r:=by
 have he:paddedCut a b s (d+1)=paddedCut a b s d+
     RCN206.directionFlag a b s:=by
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp only [paddedCut,
     RCN206.centreFlag,
     RCN206.directionFlag,
     add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
variable {Γ:Finset K} {x:I → K} {p e a b s:ℕ} [CharP (Ω K) p]
 {flag:FlagDegree} {w:ℕ}
theorem actual_identityCurveCountProvider
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀ γ∈Γ,agreements≤(S.agreementFiber γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   IdentityCurveCountProvider S (identityCurveDegree flag a b s w):=by
 classical
 unfold IdentityCurveCountProvider
 intro i hi
 dsimp only
 intro hproper
 let T:=agreementPolynomial (polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ => S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=exists_agreement_projection_of_caps S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RegularComponent (Ω K) S.G T (regularitySurface (polynomialEmbedding K) S.F)→ℕ:=
   fun C => U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=componentSeeds (Ω K) S.G T
     (regularitySurface (polynomialEmbedding K) S.F) Gi
     (selectedPoint (polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=componentSeeds_subset (Ω K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀ W:Finset (RCN346.Place (Ω K)
       (CoordinateField (Ω K) C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
       (flagSupport unitYZFlag))≤
       (coordinateDegree (Ω K) (CoordinateField (Ω K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder (Ω K)
           (CoordinateField (Ω K) C.1) v
           (coordinateValue (Ω K) (CoordinateField (Ω K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _ ≤ _:=finite_sum_coordinate_pole_le_degree (Ω K)
         (CoordinateField (Ω K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=coefficientPoleProfile_of_regular_agreement_curve
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toPrimeFlagBudgetFamily.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
       (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
       (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ) ≤
         ((U.family.toPrimeFlagBudgetFamily.zCost C+
           U.family.toPrimeFlagBudgetFamily.yzCost C:ℕ):ℤ)
       exact_mod_cast Nat.le_add_left _ _)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (polynomialEmbedding K) S.F rfl S.G_dvd_surface C
   apply prime_curve_card_le_of_coefficientPoleProfile
     (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
     (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.characteristic_bound hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact componentSeeds_on_prime (Ω K) S.G T
       (regularitySurface (polynomialEmbedding K) S.F) Gi
       (selectedPoint (polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
       hagreement γ hΓ
   · exact noLargeSelectedPencil_mono S.selected Γ Gc w e hGcΓ S.no_large_pencil
 · have hz:=U.family.sum_zDegree_le
   have hyz:=U.family.sum_yzDegree_le
   change (∑ C,U.family.toPrimeFlagBudgetFamily.zCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toPrimeFlagBudgetFamily.yzCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (mixed_padded_le_succ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (mixed_padded_le_succ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C)) ≤ identityCurveDegree flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end ProximityPrize.SubmissionLower.RCN146
end PackedLegacy_EQ

/-! Packed from ProximityPrize.SubmissionLower.O0. -/
section PackedLegacy_O0
namespace ProximityPrize.SubmissionLower.RCN268
open scoped Classical
open RCN223 RCN286 RCN174 RCN319 RCN135 RCN238 RCN243 RCN081 RCN222 RCN221 RCN266 RCN140 RCN159 RCN095 RCN275 RCN214
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Iota:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN268.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN268.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
local instance _root_.ProximityPrize.SubmissionLower.RCN268.instDecidableEqGenericField :DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def regularGeometricResidualStageOfSupport
   (support:ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
   (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
   (R:RCN266.RegularIndex Q)
   (hRirred:Irreducible R.1)
   (hRpos:0 < R.1.degreeOf (2:Fin 4))
   (hRsmall:R.1.degreeOf (2:Fin 4) < pchar)
   (hRsupport:ResidualSupportData support R.1)
   (hdegreeChar:degree < pchar)
   (g:GeometricFactor K R.1):
   letI:CharP (GenericField K) pchar:=genericField_charP K pchar
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
     x pchar errorCap (geometricFlag K g) degree support:=by
 have hsub:=regularSeeds_subset Q selected Gamma R
 exact geometricResidualStageOfSupport K support R.1 hRirred hRpos
   hRsmall hRsupport selected
   (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
   (fun gamma hgamma↦hdegree gamma (hsub hgamma))
   (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.1)
   (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.2)
   (noLargeSelectedPencil_mono selected Gamma _ degree errorCap hsub hnoPencil)
   hdegreeChar g
end
end ProximityPrize.SubmissionLower.RCN268
end PackedLegacy_O0

/-! Packed from ProximityPrize.SubmissionLower.FQ. -/

/-! Packed from ProximityPrize.SubmissionLower.AB. -/
section PackedLegacy_AB
namespace ProximityPrize.SubmissionLower.RCN259
noncomputable section
section Quotients
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def leftGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_left a b)
def rightGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_right a b)
theorem left_eq_gcd_mul_leftGCDQuotient (a b:A):
   a=gcd a b*leftGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_left a b)
theorem right_eq_gcd_mul_rightGCDQuotient (a b:A):
   b=gcd a b*rightGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_right a b)
theorem gcdQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (leftGCDQuotient a b) (rightGCDQuotient a b):=by
 intro d hdleft hdright
 have hg:gcd a b≠0:=gcd_ne_zero_of_left ha
 have hda:gcd a b*d∣a:=by
   calc
     gcd a b*d∣gcd a b*leftGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdleft
     _=a:=(left_eq_gcd_mul_leftGCDQuotient a b).symm
 have hdb:gcd a b*d∣b:=by
   calc
     gcd a b*d∣gcd a b*rightGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdright
     _=b:=(right_eq_gcd_mul_rightGCDQuotient a b).symm
 have hdg:gcd a b*d∣gcd a b:=dvd_gcd hda hdb
 apply isUnit_iff_dvd_one.mpr
 apply (mul_dvd_mul_iff_left hg).mp
 simpa only [mul_one] using hdg
end Quotients
section RecursiveDefinitions
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def gcd12 (a b:A):A:=gcd a b
def quotientA (a b:A):A:=leftGCDQuotient a b
def quotientB (a b:A):A:=rightGCDQuotient a b
theorem a_eq_gcd12_mul_quotientA (a b:A):
   a=gcd12 a b*quotientA a b:=
 left_eq_gcd_mul_leftGCDQuotient a b
theorem b_eq_gcd12_mul_quotientB (a b:A):
   b=gcd12 a b*quotientB a b:=
 right_eq_gcd_mul_rightGCDQuotient a b
theorem firstQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (quotientA a b) (quotientB a b):=
 gcdQuotients_isRelPrime ha
end RecursiveDefinitions
section Normalization
variable {A:Type*} [CommMonoidWithZero A] [NormalizedGCDMonoid A]
end Normalization
section ThreeBranchCover
variable {A B:Type*} [CommRing A] [GCDMonoid A]
 [CommRing B] [IsDomain B]
end ThreeBranchCover
end
end ProximityPrize.SubmissionLower.RCN259
end PackedLegacy_AB

/-! Packed from ProximityPrize.SubmissionLower.L3. -/
section PackedLegacy_L3
namespace ProximityPrize.SubmissionLower.RCN182
open ProximityPrize.Benchmark RCN174 RCN256 RCN319
noncomputable section
variable (K:Type*) [Field K]
end
end ProximityPrize.SubmissionLower.RCN182
end PackedLegacy_L3

/-! Packed from ProximityPrize.SubmissionLower.GF. -/
section PackedLegacy_GF
namespace ProximityPrize.SubmissionLower.RCN300
open ProximityPrize.Benchmark RCN174 RCN256 RCN319 RCN182 RCN301
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
local instance _root_.ProximityPrize.SubmissionLower.RCN300.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN300.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
end
end ProximityPrize.SubmissionLower.RCN300
end PackedLegacy_GF

/-! Packed from ProximityPrize.SubmissionLower.GD. -/
section PackedLegacy_GD
namespace ProximityPrize.SubmissionLower.RCN299
open ProximityPrize.Benchmark RCN174 RCN319 RCN259 RCN301 RCN300
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance _root_.ProximityPrize.SubmissionLower.RCN299.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN299.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN299.instGCDMonoidGlobalPoly :GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
end
end ProximityPrize.SubmissionLower.RCN299
end PackedLegacy_GD

/-! Packed from ProximityPrize.SubmissionLower.CC. -/
section PackedLegacy_CC
namespace ProximityPrize.SubmissionLower.RCN304
open ProximityPrize.Benchmark RCN319 RCN259 RCN299
noncomputable section
local instance _root_.ProximityPrize.SubmissionLower.RCN304.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN304.instDecidableEqPolynomialField :DecidableEq (Polynomial IRSProfile.Field):=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN304.instGCDMonoidGlobalPoly :GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
end
end ProximityPrize.SubmissionLower.RCN304
end PackedLegacy_CC

/-! Packed from ProximityPrize.SubmissionLower.GC. -/
section PackedLegacy_GC
namespace ProximityPrize.SubmissionLower.RCN298
open ProximityPrize.Benchmark RCN174 RCN081 RCN259 RCN301
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance _root_.ProximityPrize.SubmissionLower.RCN298.instGCDMonoidGlobalPoly :GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
end
end ProximityPrize.SubmissionLower.RCN298
end PackedLegacy_GC

/-! Packed from ProximityPrize.SubmissionLower.GH. -/
section PackedLegacy_GH
namespace ProximityPrize.SubmissionLower.RCN303
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN174 RCN319 RCN081 RCN238 RCN243 RCN259 RCN301 RCN299 RCN304 RCN298 RCN260 RCN318 RCN294 RCN291 RCN292 RCN052
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
local instance _root_.ProximityPrize.SubmissionLower.RCN303.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN303.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev StackedPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance _root_.ProximityPrize.SubmissionLower.RCN303.instGCDMonoidStackedPoly :GCDMonoid StackedPoly:=
 UniqueFactorizationMonoid.toGCDMonoid StackedPoly
local instance _root_.ProximityPrize.SubmissionLower.RCN303.instCharPFieldPrime :CharP IRSProfile.Field prime:=by
 simpa [prime,RCN223.prime] using
   RCN128.challenge_field_characteristic6600
variable {K Iota:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN303.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN303.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN303
end PackedLegacy_GH

/-! Packed from ProximityPrize.SubmissionLower.P2. -/
section PackedLegacy_P2
namespace ProximityPrize.SubmissionLower.RCN285
open scoped BigOperators Pointwise
open RCN119
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def seedlessExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1 ≤ L∧d 1 ≤ s∧d 2=0}
def seedlessBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (seedlessExponents M L s)
theorem seedlessBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈seedlessBox K M L s)
   (hg:g∈seedlessBox K M' L' s'):
   f*g∈seedlessBox K (M+M') (L+L') (s+s'):=by
 have hset:seedlessExponents M L s+seedlessExponents M' L' s' ⊆
     seedlessExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   rcases he with ⟨he0,he01,he1,he2⟩
   simp only [seedlessExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   exact ⟨by omega,by omega,by omega,by omega⟩
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_seedlessBox:
   slopeDifference K∈seedlessBox K 1 1 1:=by
 apply (seedlessBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
theorem slopeDifference_pow_mem_seedlessBox (h:ℕ):
   slopeDifference K^h∈seedlessBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [seedlessExponents]
 | succ h ih =>
     simpa only [pow_succ] using
       seedlessBox_mul K ih (slopeDifference_mem_seedlessBox K)
theorem slopeDifference_mul_mem_seedlessBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈seedlessBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈seedlessBox K M L s:=by
 have hh:=seedlessBox_mul K (slopeDifference_pow_mem_seedlessBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,
   Nat.add_sub_of_le hs] using hh
public def exponentPair (i j:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j
@[simp] public theorem exponentPair_zero (i j:ℕ):
   exponentPair i j 0=i:=by simp [exponentPair]
@[simp] public theorem exponentPair_one (i j:ℕ):
   exponentPair i j 1=j:=by simp [exponentPair]
@[simp] public theorem exponentPair_two (i j:ℕ):
   exponentPair i j 2=0:=by simp [exponentPair]
public theorem exponentPair_eta (d:Fin 3 →₀ ℕ) (hd:d 2=0):
   exponentPair (d 0) (d 1)=d:=by
 ext i
 fin_cases i <;> simp [hd]
abbrev SeedlessBoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) × Fin (min (s+1) (L+1-i.val))
public theorem fin_heq_of_val_eq
   {a b:ℕ} {u:Fin a} {v:Fin b}
   (hab:a=b) (huv:u.val=v.val):HEq u v:=by
 subst b
 exact heq_of_eq (Fin.ext huv)
def seedlessExponentsEquivIndex (M L s:ℕ):
   seedlessExponents M L s ≃ SeedlessBoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,Nat.lt_succ_of_le d.property.1⟩,
     ⟨d.val 1,by
       rcases d.property with ⟨_,h01,h1,_⟩
       rw [lt_min_iff]
       constructor
       · omega
       · change d.val 1 < L+1-d.val 0
         omega⟩⟩
 invFun q:=
   ⟨exponentPair q.1.val q.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.isLt
     rw [lt_min_iff] at hj
     simp only [seedlessExponents,Set.mem_setOf_eq,exponentPair_zero,
       exponentPair_one,exponentPair_two]
     exact ⟨by omega,by omega,by omega,by simp⟩⟩
 left_inv d:=Subtype.ext (exponentPair_eta d.val d.property.2.2.2)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact exponentPair_zero i j
   · apply fin_heq_of_val_eq
     · simp only [exponentPair_zero]
     · exact exponentPair_one i j
instance seedlessExponentsFintype (M L s:ℕ):
   Fintype (seedlessExponents M L s):=
 Fintype.ofEquiv (SeedlessBoxIndex M L s)
   (seedlessExponentsEquivIndex M L s).symm
instance seedlessBoxFinite (M L s:ℕ):
   Module.Finite K (seedlessBox K M L s):=
 Module.Finite.of_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))
def seedlessInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),min (s+1) (L+1-i)
theorem seedlessBox_finrank (M L s:ℕ):
   Module.finrank K (seedlessBox K M L s)=seedlessInputCount M L s:=by
 change Module.finrank K
     (MvPolynomial.restrictSupport K (seedlessExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))]
 rw [Fintype.card_congr (seedlessExponentsEquivIndex M L s)]
 simp [SeedlessBoxIndex,seedlessInputCount,Fintype.card_sigma,
   Finset.sum_range]
def seedlessBlockJet (M L s h:ℕ):
   seedlessBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (seedlessBox K M L s).subtype
def multiplyIntoSeedlessBox {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     seedlessBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_seedlessBox K hM hL hs q.property⟩
 map_add' q r:=by apply Subtype.ext;simp [mul_add]
 map_smul' c q:=by apply Subtype.ext;simp [mul_smul_comm]
theorem multiplyIntoSeedlessBox_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoSeedlessBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=
     slopeDifference K^h*r.val:=congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def seedlessKernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (seedlessBlockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (seedlessBlockJet K M L s h))
   (multiplyIntoSeedlessBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem seedlessKernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (seedlessKernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoSeedlessBox_injective K hM hL hs
 exact congrArg Subtype.val heq
def seedlessKernelLowerBound (M L s h:ℕ):ℕ:=
 if h ≤ M∧h ≤ L∧h ≤ s then
   seedlessInputCount (M-h) (L-h) (s-h)
 else 0
def seedlessContactRankBound (M L s h:ℕ):ℕ:=
 seedlessInputCount M L s-seedlessKernelLowerBound M L s h
theorem seedlessBlockJet_rank_le_contactRankBound
   (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (seedlessBlockJet K M L s h)) ≤
     seedlessContactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hker:=LinearMap.finrank_le_finrank_of_injective
       (seedlessKernelEmbedding_injective K hM hL hs)
     have hsum:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hker
     rw [seedlessBox_finrank K] at hsum
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_pos ⟨hM,hL,hs⟩]
     omega
   · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
       intro hh
       exact hs hh.2.2
     have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hinput
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_neg hbad,Nat.sub_zero]
     omega
 · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
     intro hh
     exact hM hh.1
   have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
   rw [seedlessBox_finrank K] at hinput
   unfold seedlessContactRankBound seedlessKernelLowerBound
   rw [if_neg hbad,Nat.sub_zero]
   omega
end
end ProximityPrize.SubmissionLower.RCN285
end PackedLegacy_P2

/-! Packed from ProximityPrize.SubmissionLower.E9. -/
section PackedLegacy_E9
namespace ProximityPrize.SubmissionLower.RCN279
open scoped BigOperators
open ProximityPrize.Benchmark RCN285 RCN119
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable (K:Type*) [Field K]
abbrev LocalPoly:=MvPolynomial (Fin 3) K
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (min 1 (L+1-i.val-j.val)) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ}
   (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 0=c.2.2.2.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 1=c.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 2=c.2.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 3=0:=by
 simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective
     (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 subst di
 subst dj
 subst de
 have hcz0:cz=0:=by omega
 have hdz0:dz=0:=by omega
 subst cz
 subst dz
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2 ≤ L∧d 2 ≤ s∧d 3=0∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):Submodule K (Poly4 K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have ht:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 have htri:c.1.val+c.2.1.val ≤ L:=by
   have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
     omega
   have hpos:0 < L+1-c.1.val-c.2.1.val:=
     hminpos.trans_le (min_le_right _ _)
   omega
 unfold globalExponents
 simp only [Set.mem_setOf_eq,columnExponent_x,columnExponent_y,
   columnExponent_r,columnExponent_z]
 exact ⟨htri,by omega,by simp,by omega⟩
def reconstruct (D w L s:ℕ) (theta:CoefficientIndex D w L s → K):
   Poly4 K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (theta c)
theorem reconstruct_coeff (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s theta)=
     theta c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro theta eta h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (htheta:theta≠0):
   reconstruct K D w L s theta≠0:=by
 intro hz
 apply htheta
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hz
theorem reconstruct_mem_box (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K):
   reconstruct K D w L s theta∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (theta c)
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     min 1 (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,
   Finset.sum_range]
def localMonomial (f j:ℕ):LocalPoly K:=
 MvPolynomial.monomial (Finsupp.single 0 f+Finsupp.single 1 j) 1
theorem localMonomial_mem (f j:ℕ):
   localMonomial K f j∈seedlessBox K f (f+j) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [localMonomial,seedlessExponents]
def blockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):LocalPoly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     ((((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)*u^(c.1.val-f.val))) •
         localMonomial K f.val c.2.1.val
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u c r∈
     seedlessBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (seedlessBox K (min r L) L s).smul_mem
   apply MvPolynomial.restrictSupport_mono (R:=K) ?_
     (localMonomial_mem K f.val c.2.1.val)
   intro d hd
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have ht:=c.2.2.1.isLt
   have hfi:=f.isLt
   have htri:c.1.val+c.2.1.val ≤ L:=by
     have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
       omega
     have hpos:0 < L+1-c.1.val-c.2.1.val:=
       hminpos.trans_le (min_le_right _ _)
     omega
   exact ⟨hd0.trans (by omega),by omega,hd1.trans (by omega),hd2⟩
 · exact (seedlessBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   seedlessBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u c r,blockEntry_mem K D w L s x u c r⟩
def extractBlock (D w L s:ℕ) (x u:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     seedlessBox K (min r L) L s where
 toFun theta:=∑ c:CoefficientIndex D w L s,
   theta c • boundedBlockEntry K D w L s x u c r
 map_add' theta eta:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a theta:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,
     RingHom.id_apply]
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   seedlessContactRankBound (min r L) L s (m-r)
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 exact seedlessBlockJet_rank_le_contactRankBound K (min r.val L) L s
   (m-r.val) (min_le_right r.val L)
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (seedlessBlockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (received i) r.val)
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (hgate:Fintype.card I*localRankBound m L s <
     coefficientCount D w L s):
   ∃ theta:CoefficientIndex D w L s → K,theta≠0∧
     constraintMap K D w L s m nodes received theta=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective
     (constraintMap K D w L s m nodes received):=by
   intro theta eta heq
   by_contra hne
   apply hnone
   refine ⟨theta-eta,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have htarget:Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
   change Module.finrank K (I → LocalTarget K m L s) ≤ _
   rw [Module.finrank_pi_fintype]
   calc
     (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
         ∑ _i:I,localRankBound m L s:=by
       apply Finset.sum_le_sum
       intro i hi
       exact localTarget_finrank_le K m L s
     _=Fintype.card I*localRankBound m L s:=by simp
 exact (Nat.not_le_of_gt hgate) (hdim.trans htarget)
theorem all_blocks_divisible_of_kernel {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (theta:CoefficientIndex D w L s → K)
   (hzero:constraintMap K D w L s m nodes received theta=0):
   ∀ i:I,∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K):=by
 intro i r
 by_cases hr:r < m
 · have hh:=congrArg
     (fun t:GlobalTarget K I m L s => ((t i ⟨r,hr⟩):LocalPoly K)) hzero
   change contactJet K (m-r)
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K)=0 at hh
   exact (contactJet_eq_zero_iff K (m-r) _).mp hh
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
def homogenizedTranslation (x u:K):
   Poly4 K →ₐ[K] Polynomial (LocalPoly K):=
 RCN122.homogenizedTranslation K x u 0
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j:ℕ):
   localMonomial K f j=MvPolynomial.X 0^f*MvPolynomial.X 1^j:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   ←MvPolynomial.X_pow_eq_monomial]
theorem translation_column_coeff (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u c r:=by
 have hfactor:
     homogenizedTranslation K x u
         (MvPolynomial.monomial (columnExponent c) a)=
       Polynomial.C (MvPolynomial.C a)*
         (((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
           (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
             Polynomial.C (MvPolynomial.C u))^c.1.val*
           Polynomial.C (MvPolynomial.X 1^c.2.1.val))):=by
   rw [columnMonomial_eq K D w L s]
   simp [homogenizedTranslation,
     RCN122.homogenizedTranslation,
     RCN122.translationVariables,
     RCN100.seedAffine,
     Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,
   RCN122.coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,map_mul,
     map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u:K)
   (theta:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u (reconstruct K D w L s theta)).coeff r=
     ((extractBlock K D w L s x u r theta):LocalPoly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
     theta c • blockEntry K D w L s x u c r)=
   (((∑ c:CoefficientIndex D w L s,
     theta c • boundedBlockEntry K D w L s x u c r):
       seedlessBox K (min r L) L s):LocalPoly K)
 simp [boundedBlockEntry]
end
end ProximityPrize.SubmissionLower.RCN279
end PackedLegacy_E9

/-! Packed from ProximityPrize.SubmissionLower.O9. -/
section PackedLegacy_O9
namespace ProximityPrize.SubmissionLower.RCN282
open scoped Classical BigOperators
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN229 RCN065 RCN238 RCN173 RCN264 RCN243 RCN319 RCN163
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
local instance _root_.ProximityPrize.SubmissionLower.RCN282.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN282.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
def seedlessPoint (S:Polynomial K):Fin 3 → Omega:=
 fun i => polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X) i.succ
theorem seedlessPoint_value (S:Polynomial K):
   seedlessPoint phi S=![phi S,phi S.derivative,0]:=by
 funext i
 fin_cases i <;>
   simp [seedlessPoint,polynomialPoint,polynomial_eval₂_comp_C_X]
theorem seedlessPoint_injective (hphi:Function.Injective phi):
   Function.Injective (seedlessPoint phi):=by
 intro S T h
 apply hphi
 have h0:=congrFun h (0:Fin 3)
 simpa only [seedlessPoint_value,Matrix.cons_val_zero] using h0
theorem seedlessPoint_surface_evaluation (S:Polynomial K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (seedlessPoint phi S) (surfaceMap phi Q)=
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X)) Q:=by
 rw [eval_surfaceMap]
 have hv:Fin.cases (phi Polynomial.X) (seedlessPoint phi S)=
     polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
theorem seedless_agreement_zero_iff
   (F:MvPolynomial (Fin 4) K) (S:Polynomial K)
   (p w:ℕ) [CharP Omega p] (hchar:w < p)
   (hdegree:S.natDegree ≤ w)
   (hsolution:specialization K S 0 F=0)
   (hregular:MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u:K):
   MvPolynomial.aeval (seedlessPoint phi S)
     (agreementPolynomial phi F w x u 0)=0 ↔ S.eval x=u:=by
 have hpoint:seedlessPoint phi S=selectedPoint phi (fun _:K => S) 0:=rfl
 rw [hpoint]
 simpa only [zero_mul,add_zero] using
   (selected_agreement_zero_iff phi F (fun _:K => S) p w hchar 0
     hdegree hsolution hregular x u 0)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
theorem seedless_agreement_fiber_card_le
   (hphi:Function.Injective phi)
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
   (p w:ℕ) [CharP Omega p] (hchar:w < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ S∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
   (x u:K) (hproper:agreementPolynomial phi F w x u 0∉P)
   (cap:Fin 3 → ℕ)
   (hcap:∀ j,(agreementPolynomial phi F w x u 0).degreeOf j ≤ cap j):
   (Gamma.filter (fun S => S.eval x=u)).card ≤ componentCost P cap:=by
 classical
 let fiber:=Gamma.filter (fun S => S.eval x=u)
 let points:=fiber.image (seedlessPoint phi)
 have hpointsP:∀ v∈points,
     P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint S (Finset.mem_filter.mp hS).1
 have hpointsF:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial phi F w x u 0)=0:=by
   intro v hv
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hS
   exact (seedless_agreement_zero_iff phi F S p w hchar
     (hdegree S hGamma) (hsolution S hGamma) (hregular S hGamma) x u).mpr hagree
 have hcount:=RCN007.finite_zero_points_le_box Omega P hproj
   hnonpoint (agreementPolynomial phi F w x u 0) hproper cap hcap
   points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (seedlessPoint_injective phi hphi)
 rw [hcard] at hcount
 unfold componentCost
 exact_mod_cast hcount
theorem coordinate_two_eq_zero (hZ:MvPolynomial.X (2:Fin 3)∈P):
   coordinate Omega P 2=0:=by
 change coordinateEvaluation Omega P (MvPolynomial.X (2:Fin 3))=0
 change MvPolynomial.X (2:Fin 3)∈
   RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rwa [coordinateEvaluation_ker]
theorem identityNodes_card_le_of_seedless_cut
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (hZ:MvPolynomial.X (2:Fin 3)∈P)
   {Iota:Type} (nodes:Finset Iota) (x u:Iota → K)
   (w:ℕ) (hw:1 ≤ w) (hinj:Set.InjOn x nodes)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   (identityNodes phi P F nodes x u (fun _ => 0) w).card ≤ w:=by
 classical
 by_contra hnot
 have hmany:w < (identityNodes phi P F nodes x u (fun _ => 0) w).card:=
   Nat.lt_of_not_ge hnot
 have htrans:=seed_transcendental_of_many_identities phi P F hF hH
   nodes x u (fun _ => 0) w hw hinj hmany hnonpoint
 have hz0:=coordinate_two_eq_zero P hZ
 rw [hz0] at htrans
 exact htrans isAlgebraic_zero
variable {Iota:Type}
local instance _root_.ProximityPrize.SubmissionLower.RCN282.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
theorem seedless_prime_incidence
   (hphi:Function.Injective phi)
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (hZ:MvPolynomial.X (2:Fin 3)∈P)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ S∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤ (nodes.card-w)*componentCost P cap:=by
 classical
 let I:=identityNodes phi P F nodes x u (fun _ => 0) w
 let relation:Polynomial K → Iota → Prop:=fun S i => S.eval (x i)=u i
 have hI:I.card ≤ w:=identityNodes_card_le_of_seedless_cut phi P F hF hH
   hZ nodes x u w hw hinj hnonpoint
 have hfiber:∀ i∈nodes \ I,
     (Gamma.filter (fun S => relation S i)).card ≤ componentCost P cap:=by
   intro i hi
   obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
   have hproper:agreementPolynomial phi F w (x i) (u i) 0∉P:=by
     intro hmem
     apply hnotI
     exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
   exact seedless_agreement_fiber_card_le phi P hphi hproj hnonpoint F Gamma
     p w hchar hdegree hsolution hregular hpoint (x i) (u i) hproper cap
     (hcap i hinodes)
 exact sharp_incidence_bound relation Gamma nodes I a w (componentCost P cap)
   (identityNodes_subset phi P F nodes x u (fun _ => 0) w) hI hwa han
   hagreement hfiber
end
end ProximityPrize.SubmissionLower.RCN282
end PackedLegacy_O9

/-! Packed from ProximityPrize.SubmissionLower.P0. -/
section PackedLegacy_P0
namespace ProximityPrize.SubmissionLower.RCN283
open scoped Classical BigOperators
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN282
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
local instance _root_.ProximityPrize.SubmissionLower.RCN283.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN283.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN283.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
def seedlessCut:MvPolynomial (Fin 3) Omega:=MvPolynomial.X 2
theorem seedless_proper_cut_bound
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Omega)
   (hG:Irreducible G) (hdiv:G∣surfaceMap phi F)
   (hproper:¬ G∣seedlessCut)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     (seedlessCut (Omega:=Omega)).degreeOf j*G.degreeOf k+
       G.degreeOf j*(seedlessCut (Omega:=Omega)).degreeOf k < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) G=0)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤
     (nodes.card-w)*
       (∑ i,cap i*coordinateMixedDegree Omega G seedlessCut i):=by
 classical
 let T:MvPolynomial (Fin 3) Omega:=seedlessCut
 let H:=regularitySurface phi F
 have hTpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) T=0:=by
   intro S hS
   simp [T,seedlessCut,seedlessPoint_value]
 have hHp:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) H≠0:=by
   intro S hS
   change MvPolynomial.eval (seedlessPoint phi S)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [seedlessPoint_surface_evaluation]
   exact hregular S hS
 let degree:RegularComponent Omega G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Omega C.1 i
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C).card*
         (a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i):=by
   intro C
   have hsub:=componentSeeds_subset Omega G T H Gamma (seedlessPoint phi) C
   have hgmem:=regularComponent_G_mem Omega G T H C
   have htmem:=regularComponent_T_mem Omega G T H C
   have hFmem:surfaceMap phi F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Omega C.1:=
     all_transcendental_coordinates_finite_separable Omega C.1 p G T
       hG hgmem htmem hproper hGdegree hcutDegree
   exact seedless_prime_incidence phi C.1 hphi hproj
     (regularComponent_ne_point Omega G T H C) F hFmem
     (regularComponent_H_not_mem Omega G T H C) htmem
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C)
     nodes x u hinj p w a hw hchar hwa han
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolution S (hsub hS))
     (fun S hS => hregular S (hsub hS))
     (fun S hS => componentSeeds_on_prime Omega G T H Gamma
       (seedlessPoint phi) C S hS)
     (fun S hS => hagreement S (hsub hS)) cap hcap
 have hbudget:∀ i,
     (∑ C:RegularComponent Omega G T H,
       actualCoordinateDegree Omega C.1 i) ≤
         coordinateMixedDegree Omega G T i:=
   regularComponents_degree_budget phi F G T p hG hproper hGdegree hcutDegree
 have hagg:=aggregate_component_incidence Omega G T H Gamma
   (seedlessPoint phi) hGpoint hTpoint hHp (a-w) (nodes.card-w) 0
   cap (coordinateMixedDegree Omega G T) degree
   (fun C => by simpa only [Nat.zero_mul,Nat.add_zero] using hcomponent C)
   hbudget
 simpa only [T,Nat.zero_mul,Nat.add_zero] using hagg
end
end ProximityPrize.SubmissionLower.RCN283
end PackedLegacy_P0

/-! Packed from ProximityPrize.SubmissionLower.O8. -/
section PackedLegacy_O8
namespace ProximityPrize.SubmissionLower.RCN281
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def prime:ℕ:=2130706433
variable (K:Type) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN281.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN281.instDecidableEqGenericField :DecidableEq (GenericField K):=Classical.decEq (GenericField K)
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 RCN222.GeometricFactor K F
def geometricPolynomials (F:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)) (g:GeometricFactor K F):
   Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S =>
   MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S) g.1=0)
theorem geometricPolynomials_subset
   (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
   (g:GeometricFactor K F):geometricPolynomials K F Gamma g ⊆ Gamma:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricPolynomials
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,specialization K S 0 F=0):
   Gamma.card ≤ ∑ g:GeometricFactor K F,
     (geometricPolynomials K F Gamma g).card:=by
 classical
 have hcover:Gamma ⊆ Finset.univ.biUnion (geometricPolynomials K F Gamma):=by
   intro S hS
   have hz:MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [seedlessPoint_surface_evaluation,
       eval_polynomialPoint_eq_specialization,hsolutions S hS]
     simp
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (seedlessPoint (polynomialEmbedding K) S) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hS,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometric_seedless_cut_proper
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hR:0 < g.degreeOf 1):
   ¬ g∣(seedlessCut:MvPolynomial (Fin 3) (GenericField K)):=by
 intro hdvd
 have hle:=coordinate_degree_le_of_dvd 1 g seedlessCut hdvd
   (by simp [seedlessCut])
 have hx:(seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
   simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
 rw [hx] at hle
 omega
def yProjection (T:Type*) [Field T]:
   MvPolynomial (Fin 3) T →+*Polynomial T:=
 MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0]
def yEmbedding (T:Type*) [Field T]:
   Polynomial T →+*MvPolynomial (Fin 3) T:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
theorem y_only_vars {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
   (i:Fin 3) (hi:i∈S.vars):i=0:=by
 fin_cases i
 · rfl
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hZ)
theorem yProjection_reconstruct {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
   yEmbedding T (yProjection T S)=S:=by
 change ((yEmbedding T).comp (yProjection T)) S=(RingHom.id _) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [yEmbedding,yProjection]
 · intro i hi _
   rw [y_only_vars S hR hZ i hi]
   simp [yEmbedding,yProjection]
 · rfl
theorem yProjection_nonzero {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T) (hS:S≠0)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
   yProjection T S≠0:=by
 intro hz
 apply hS
 rw [←yProjection_reconstruct S hR hZ,hz,map_zero]
theorem yProjection_natDegree_le {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T):
   (yProjection T S).natDegree ≤ S.degreeOf 0:=by
 classical
 have hsum:yProjection T S=
     ∑ d∈S.support,yProjection T (MvPolynomial.monomial d (S.coeff d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 rw [hsum]
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro d hd
 have hmono:(yProjection T (MvPolynomial.monomial d (S.coeff d))).natDegree ≤
     d 0:=by
   have heq:MvPolynomial.monomial d (S.coeff d)=
       MvPolynomial.C (S.coeff d)*MvPolynomial.X 0^d 0*
         MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
     exact RCN080.monomial_fin3 d (S.coeff d)
   rw [heq]
   by_cases h1:d 1=0 <;> by_cases h2:d 2=0 <;>
     simp [yProjection,h1,h2]
   have hc:(Polynomial.C (S.coeff d)).natDegree ≤ 0:=by simp
   have hx:((Polynomial.X:Polynomial T)^d 0).natDegree ≤ d 0:=by simp
   simpa only [Nat.zero_add] using Polynomial.natDegree_mul_le_of_le hc hx
 exact hmono.trans (MvPolynomial.monomial_le_degreeOf 0 hd)
theorem yProjection_eval {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
   (v:Fin 3 → T):
   (yProjection T S).eval (v 0)=MvPolynomial.eval v S:=by
 change ((Polynomial.evalRingHom (v 0)).comp (yProjection T)) S=
   (MvPolynomial.eval v) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [yProjection]
 · intro i hi _
   rw [y_only_vars S hR hZ i hi]
   simp [yProjection]
 · rfl
def yWeights:Fin 4 → ℕ:=![0,1,0,0]
def zWeights:Fin 4 → ℕ:=![0,0,0,1]
theorem degreeY_le_yWeight (Q:MvPolynomial (Fin 4) K):
   Q.degreeOf 1 ≤ MvPolynomial.weightedTotalDegree yWeights Q:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=MvPolynomial.le_weightedTotalDegree yWeights hd
 rw [weight_fin4] at h
 simpa [yWeights] using h
theorem degreeZ_le_zWeight (Q:MvPolynomial (Fin 4) K):
   Q.degreeOf 3 ≤ MvPolynomial.weightedTotalDegree zWeights Q:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=MvPolynomial.le_weightedTotalDegree zWeights hd
 rw [weight_fin4] at h
 simpa [zWeights] using h
def singularPolynomials (Q:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)):Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S => specialization K S 0 (singularAuxiliary Q)=0)
def regularPolynomials (Q:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)) (F:↥(positiveRFactors Q)):
   Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S => RegularSolution F.1 S 0)
theorem seedless_solution_cover
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0):
   Gamma.card ≤ (singularPolynomials K Q Gamma).card+
     ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=by
 classical
 let regularUnion:=Finset.univ.biUnion (regularPolynomials K Q Gamma)
 have hcover:Gamma ⊆ singularPolynomials K Q Gamma ∪ regularUnion:=by
   intro S hS
   obtain hsing | ⟨F,hF,hreg⟩:=solution_regular_or_auxiliary
     Q hQ S 0 (hsolutions S hS)
   · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hsing⟩)
   · apply Finset.mem_union_right
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨F,hF⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hS,hreg⟩⟩
 calc
   Gamma.card ≤ (singularPolynomials K Q Gamma ∪ regularUnion).card:=
     Finset.card_le_card hcover
   _ ≤ (singularPolynomials K Q Gamma).card+regularUnion.card:=
     Finset.card_union_le _ _
   _ ≤ (singularPolynomials K Q Gamma).card+
       ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=
     Nat.add_le_add_left Finset.card_biUnion_le _
end
end ProximityPrize.SubmissionLower.RCN281
end PackedLegacy_O8

/-! Packed from ProximityPrize.SubmissionLower.H7. -/
section PackedLegacy_H7
namespace ProximityPrize.SubmissionLower.RCN020
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
end Proofs
end ProximityPrize.SubmissionLower.RCN020
end PackedLegacy_H7

/-! Packed from ProximityPrize.SubmissionLower.H6. -/
section PackedLegacy_H6
namespace ProximityPrize.SubmissionLower.RCN019
open scoped BigOperators
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
 {r:ℕ}
def rowPolynomial (v:Fin r → F):Polynomial F:=
 ∑ j:Fin r,Polynomial.monomial j.val (v j)
theorem rowPolynomial_coeff (v:Fin r → F) (j:Fin r):
   (rowPolynomial v).coeff j.val=v j:=by
 classical
 rw [rowPolynomial,Polynomial.finsetSum_coeff]
 calc
   (∑ k:Fin r,(Polynomial.monomial k.val (v k)).coeff j.val)=
       (Polynomial.monomial j.val (v j)).coeff j.val:=by
     apply Finset.sum_eq_single j
     · intro k _ hkj
       have hval:k.val≠j.val:=fun hh => hkj (Fin.ext hh)
       simp [Polynomial.coeff_monomial,hval,Ne.symm hval]
     · intro hnot
       exact (hnot (Finset.mem_univ j)).elim
   _=v j:=by simp [Polynomial.coeff_monomial]
theorem rowPolynomial_injective:
   Function.Injective (rowPolynomial:(Fin r → F) → Polynomial F):=by
 intro v u heq
 funext j
 have hc:=congrArg (fun P:Polynomial F => P.coeff j.val) heq
 simpa only [rowPolynomial_coeff] using hc
theorem rowPolynomial_natDegree_le (v:Fin r → F):
   (rowPolynomial v).natDegree ≤ r-1:=by
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro j _
 have hterm:=Polynomial.natDegree_monomial_le (v j) (m:=j.val)
 have hj:=j.isLt
 exact hterm.trans (by omega)
def momentProjection (t:F) (v:ι → Fin r → F):ι → F:=
 fun i => (rowPolynomial (v i)).eval t
theorem momentProjection_apply (t:F) (v:ι → Fin r → F) (i:ι):
   momentProjection t v i=∑ j:Fin r,t^j.val*v i j:=by
 change (Polynomial.evalRingHom t)
     (∑ j:Fin r,Polynomial.monomial j.val (v i j))=_
 rw [map_sum]
 apply Finset.sum_congr rfl
 intro j _
 change (Polynomial.monomial j.val (v i j)).eval t=t^j.val*v i j
 rw [Polynomial.eval_monomial,mul_comm]
theorem exists_nonzero_coordinate_difference
   (v u:ι → Fin r → F) (hne:v≠u):
   ∃ P:Polynomial F,P≠0∧P.natDegree ≤ r-1∧
     ∀ t:F,momentProjection t v=momentProjection t u → P.eval t=0:=by
 classical
 obtain ⟨i,hi⟩:∃ i:ι,v i≠u i:=by
   by_contra hno
   push_neg at hno
   exact hne (funext hno)
 refine ⟨rowPolynomial (v i)-rowPolynomial (u i),?_,?_,?_⟩
 · apply sub_ne_zero.mpr
   intro hh
   exact hi (rowPolynomial_injective hh)
 · exact (Polynomial.natDegree_sub_le _ _).trans
     (max_le (rowPolynomial_natDegree_le _) (rowPolynomial_natDegree_le _))
 · intro t ht
   rw [Polynomial.eval_sub]
   exact sub_eq_zero.mpr (congrFun ht i)
def pairCollisionSeeds (pair:Finset (ι → Fin r → F)):Finset F:=by
 classical
 exact Finset.univ.filter (fun t => ∃ v∈pair,∃ u∈pair,
   v≠u∧momentProjection t v=momentProjection t u)
theorem mem_pairCollisionSeeds_iff
   (pair:Finset (ι → Fin r → F)) (t:F):
   t∈pairCollisionSeeds pair ↔ ∃ v∈pair,∃ u∈pair,
     v≠u∧momentProjection t v=momentProjection t u:=by
 classical
 simp only [pairCollisionSeeds,Finset.mem_filter,Finset.mem_univ,true_and]
theorem pairCollisionSeeds_card_le
   (pair:Finset (ι → Fin r → F)) (hpair:pair.card=2):
   (pairCollisionSeeds pair).card ≤ r-1:=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 obtain ⟨v,u,hne,rfl⟩:=Finset.card_eq_two.mp hpair
 obtain ⟨P,hP,hdegree,heval⟩:=exists_nonzero_coordinate_difference v u hne
 have hcard:(pairCollisionSeeds ({v,u}:Finset (ι → Fin r → F))).card ≤
     P.natDegree:=by
   apply Polynomial.card_le_degree_of_subset_roots
   intro t ht
   apply (Polynomial.mem_roots hP).mpr
   apply heval t
   have ht':t∈pairCollisionSeeds ({v,u}:Finset (ι → Fin r → F)):=ht
   obtain ⟨a,ha,b,hb,hab,habproj⟩:=
     (mem_pairCollisionSeeds_iff ({v,u}:Finset (ι → Fin r → F)) t).mp ht'
   simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
   rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
   · exact (hab rfl).elim
   · exact habproj
   · exact habproj.symm
   · exact (hab rfl).elim
 exact hcard.trans hdegree
def allCollisionSeeds (L:Finset (ι → Fin r → F)):Finset F:=by
 classical
 exact (L.powersetCard 2).biUnion pairCollisionSeeds
theorem allCollisionSeeds_card_le (L:Finset (ι → Fin r → F)):
   (allCollisionSeeds L).card ≤ (r-1)*L.card.choose 2:=by
 classical
 calc
   (allCollisionSeeds L).card ≤
       ∑ pair∈L.powersetCard 2,(pairCollisionSeeds pair).card:=
     Finset.card_biUnion_le
   _ ≤ ∑ _pair∈L.powersetCard 2,(r-1):=by
     apply Finset.sum_le_sum
     intro pair hpair
     exact pairCollisionSeeds_card_le pair (Finset.mem_powersetCard.mp hpair).2
   _=(L.powersetCard 2).card*(r-1):=by simp
   _=(r-1)*L.card.choose 2:=by
     rw [Finset.card_powersetCard,Nat.mul_comm]
theorem exists_separating_moment_parameter
   (L:Finset (ι → Fin r → F))
   (hfield:(r-1)*L.card.choose 2 < Fintype.card F):
   ∃ t:F,Set.InjOn (momentProjection (ι:=ι) (r:=r) t)
     (L:Set (ι → Fin r → F)):=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 have hsmall:(allCollisionSeeds L).card < Fintype.card F:=
   (allCollisionSeeds_card_le L).trans_lt hfield
 obtain ⟨t,ht⟩:∃ t:F,t∉allCollisionSeeds L:=by
   by_contra hno
   have hsub:Finset.univ ⊆ allCollisionSeeds L:=by
     intro t _
     by_contra ht
     exact hno ⟨t,ht⟩
   have hc:=Finset.card_le_card hsub
   rw [Finset.card_univ] at hc
   omega
 refine ⟨t,?_⟩
 intro v hv u hu hproj
 change v∈L at hv
 change u∈L at hu
 by_contra hne
 apply ht
 apply Finset.mem_biUnion.mpr
 refine ⟨{v,u},?_,?_⟩
 · apply Finset.mem_powersetCard.mpr
   constructor
   · intro c hc
     simp only [Finset.mem_insert,Finset.mem_singleton] at hc
     rcases hc with rfl | rfl
     · exact hv
     · exact hu
   · simp [hne]
 · apply (mem_pairCollisionSeeds_iff ({v,u}:Finset (ι → Fin r → F)) t).mpr
   exact ⟨v,by simp,u,by simp,hne,hproj⟩
theorem momentProjection_mem_code
   (C:LinearCode ι F) (t:F) (v:ι → Fin r → F)
   (hrows:∀ j:Fin r,(fun i => v i j)∈C):
   momentProjection t v∈C:=by
 classical
 have heq:momentProjection t v=
     ∑ j:Fin r,t^j.val • (fun i => v i j):=by
   funext i
   rw [momentProjection_apply]
   simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
 rw [heq]
 exact C.sum_mem (fun j _ => C.smul_mem (t^j.val) (hrows j))
theorem momentProjection_preserves_agreements
   (t:F) (v u:ι → Fin r → F):
   (Finset.univ.filter (fun i => v i=u i)) ⊆
     Finset.univ.filter (fun i => momentProjection t v i=momentProjection t u i):=by
 classical
 intro i hi
 refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
 have hv:=(Finset.mem_filter.mp hi).2
 change (rowPolynomial (v i)).eval t=(rowPolynomial (u i)).eval t
 rw [hv]
end Proofs
end ProximityPrize.SubmissionLower.RCN019
end PackedLegacy_H6

/-! Packed from ProximityPrize.SubmissionLower.H5. -/
section PackedLegacy_H5
namespace ProximityPrize.SubmissionLower.RCN018
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section DraftProofs
section RadiusCell
variable {ι A:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [DecidableEq A]
theorem agreement_card_ge_of_closeCodewordsRel
   (C:Set (ι → A)) (y c:ι → A) (δ:ℝ) (e:ℕ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ))
   (hc:c∈Code.closeCodewordsRel C y δ):
   Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => c i=y i)).card:=by
 classical
 have hball:=(Code.mem_closeCodewordsRel_iff.mp hc).2
 simp only [Code.relHammingDist_coe] at hball
 have hn:(0:ℝ) < (Fintype.card ι:ℝ):=by
   exact_mod_cast Fintype.card_pos
 have hdistR:(hammingDist y c:ℝ) < ((e+1:ℕ):ℝ):=
   ((div_le_iff₀ hn).mp hball).trans_lt hcell
 have hdist:hammingDist y c ≤ e:=by
   have hlt:hammingDist y c < e+1:=by exact_mod_cast hdistR
   omega
 have hagree:Code.agree c y+hammingDist y c=Fintype.card ι:=by
   rw [hammingDist_comm]
   exact Code.agree_add_hammingDist (u:=c) (v:=y)
 change Fintype.card ι-e ≤ Code.agree c y
 omega
end RadiusCell
section GenericCode
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
def sixteenIndexEquiv:Fin 2 × Fin 8 ≃ Fin 16:=finProdFinEquiv
def flattenSymbol (v:Fin 2 → Fin 8 → F) (j:Fin 16):F:=
 v (sixteenIndexEquiv.symm j).1 (sixteenIndexEquiv.symm j).2
def unflattenSymbol (v:Fin 16 → F) (a:Fin 2) (b:Fin 8):F:=
 v (sixteenIndexEquiv (a,b))
theorem unflatten_flattenSymbol (v:Fin 2 → Fin 8 → F):
   unflattenSymbol (flattenSymbol v)=v:=by
 funext a b
 simp only [unflattenSymbol,flattenSymbol,Equiv.symm_apply_apply]
theorem flatten_unflattenSymbol (v:Fin 16 → F):
   flattenSymbol (unflattenSymbol v)=v:=by
 funext j
 change v (sixteenIndexEquiv (sixteenIndexEquiv.symm j))=v j
 rw [Equiv.apply_symm_apply]
def squaredEightSymbolEquiv:(Fin 2 → Fin 8 → F) ≃ (Fin 16 → F) where
 toFun:=flattenSymbol
 invFun:=unflattenSymbol
 left_inv:=unflatten_flattenSymbol
 right_inv:=flatten_unflattenSymbol
def flattenWord (v:ι → Fin 2 → Fin 8 → F):ι → Fin 16 → F:=
 fun i => squaredEightSymbolEquiv (v i)
theorem flattenWord_injective:
   Function.Injective (flattenWord:(ι → Fin 2 → Fin 8 → F) → ι → Fin 16 → F):=by
 intro v u h
 funext i
 exact squaredEightSymbolEquiv.injective (congrFun h i)
theorem flattenWord_agreement_iff
   (v u:ι → Fin 2 → Fin 8 → F) (i:ι):
   flattenWord v i=flattenWord u i ↔ v i=u i:=by
 constructor
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i) at hh
   exact (squaredEightSymbolEquiv (F:=F)).injective hh
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i)
   exact congrArg (squaredEightSymbolEquiv (F:=F)) hh
theorem flattenWord_agreement_card (v u:ι → Fin 2 → Fin 8 → F):
   (Finset.univ.filter (fun i => flattenWord v i=flattenWord u i)).card=
     (Finset.univ.filter (fun i => v i=u i)).card:=by
 classical
 congr 1
 ext i
 simp only [Finset.mem_filter,flattenWord_agreement_iff]
theorem squared_eight_rows
   (C:LinearCode ι F) (v:ι → Fin 2 → Fin 8 → F)
   (hv:v∈((C^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode ι F (Fin 2 → Fin 8 → F))):
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈C:=by
 intro a b
 have houter:=
   (Code.mem_moduleInterleavedCode_iff F (Fin 8 → F) (Fin 2) ι
     (C^⋈ (Fin 8)) v).mp hv a
 exact (Code.mem_moduleInterleavedCode_iff F F (Fin 8) ι C _).mp houter b
end GenericCode
theorem irs_code_mem_iff_rows
   (v:IRSProfile.Index → Fin IRSProfile.interleaving → IRSProfile.Field):
   v∈IRSProfile.code ↔
     ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode:=by
 change (∀ b:Fin IRSProfile.interleaving,
   (fun i => v i b)∈ReedSolomon.code IRSProfile.domain
     (IRSProfile.totalDimension/IRSProfile.interleaving)) ↔ _
 rw [IRSProfile.totalDimension_div_interleaving]
 rfl
theorem irs_squared_carrier_eq:
   (((IRSProfile.code^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field
       (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)))=
   ((((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin 8 → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))):=by
 ext v
 change (∀ a:Fin 2,(fun i => v i a)∈IRSProfile.code) ↔
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈IRSProfile.baseCode
 constructor
 · intro hv a b
   exact (irs_code_mem_iff_rows _).mp (hv a) b
 · intro hv a
   exact (irs_code_mem_iff_rows _).mpr (hv a)
end DraftProofs
end ProximityPrize.SubmissionLower.RCN018
end PackedLegacy_H5

/-! Packed from ProximityPrize.SubmissionLower.F0. -/
section PackedLegacy_F0
namespace ProximityPrize.SubmissionLower.RCN280
open scoped Classical NNReal
open ProximityPrize.Benchmark RCN279 RCN281 RCN019 RCN018 RCN319
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
local instance _root_.ProximityPrize.SubmissionLower.RCN280.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN280.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN280.instCharPFieldPrime :CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem squared_eight_lambda_le_of_interleaved_list
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (e B:ℕ)
   (hfinite:∀ (received:ι → Fin 16 → F)
       (L:Finset (ι → Fin 16 → F)),
     (∀ v∈L,∀ j:Fin 16,(fun i => v i j)∈C) →
     (∀ v∈L,Fintype.card ι-e ≤
       (Finset.univ.filter (fun i => v i=received i)).card) →
     L.card ≤ B)
   (delta:ℝ)
   (hcell:delta*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) delta ≤ (B:ℕ∞):=by
 classical
 letI:DecidableEq (ι → Fin 2 → Fin 8 → F):=Classical.decEq _
 letI:DecidableEq (ι → Fin 16 → F):=Classical.decEq _
 apply Code.Lambda_le_of_forall_finset_card_le
 intro received L hL
 let projected:Finset (ι → Fin 16 → F):=L.image flattenWord
 have hinj:Set.InjOn flattenWord (L:Set (ι → Fin 2 → Fin 8 → F)):=
   fun _ _ _ _ hh => flattenWord_injective hh
 have hcard:projected.card=L.card:=Finset.card_image_of_injOn hinj
 have hrows:∀ v∈projected,∀ j:Fin 16,(fun i => v i j)∈C:=by
   intro v hv j
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hL c hc)).1
   change (fun i => c i (sixteenIndexEquiv.symm j).1
     (sixteenIndexEquiv.symm j).2)∈C
   exact squared_eight_rows C c hcode _ _
 have hclose:∀ v∈projected,Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => v i=flattenWord received i)).card:=by
   intro v hv
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   rw [flattenWord_agreement_card]
   exact agreement_card_ge_of_closeCodewordsRel _ received c delta e hcell (hL c hc)
 have hbound:=hfinite (flattenWord received) projected hrows hclose
 rwa [hcard] at hbound
end
end ProximityPrize.SubmissionLower.RCN280
end PackedLegacy_F0

/-! Packed from ProximityPrize.SubmissionLower.O7. -/
section PackedLegacy_O7
namespace ProximityPrize.SubmissionLower.RCN278
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
end
end ProximityPrize.SubmissionLower.RCN278
end PackedLegacy_O7

/-! Packed from ProximityPrize.SubmissionLower.P1. -/
section PackedLegacy_P1
namespace ProximityPrize.SubmissionLower.RCN284
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
theorem field_cardinality:
   Fintype.card IRSProfile.Field=(2130706433:ℕ)^6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem irs_code_eq_base_interleaved:
   IRSProfile.code=
     (IRSProfile.baseCode^⋈ (Fin IRSProfile.interleaving):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin IRSProfile.interleaving → IRSProfile.Field)):=by
 ext v
 change v∈IRSProfile.code ↔
   ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode
 exact RCN018.irs_code_mem_iff_rows v
theorem nat_div_le_inv_pow {m q t:ℕ} (hm:0 < m)
   (hq:m*2^t ≤ q):
   (m:ENNReal)/(q:ENNReal) ≤ 1/2^t:=by
 have hm0:(m:ENNReal)≠0:=by exact_mod_cast hm.ne'
 have hmtop:(m:ENNReal)≠⊤:=ENNReal.natCast_ne_top m
 have hqE:((m*2^t:ℕ):ENNReal) ≤ (q:ENNReal):=by
   exact_mod_cast hq
 have hcast:((m*2^t:ℕ):ENNReal)=(m:ENNReal)*2^t:=by
   push_cast
   ring
 calc
   (m:ENNReal)/(q:ENNReal) ≤
       (m:ENNReal)/((m*2^t:ℕ):ENNReal):=
     ENNReal.div_le_div_left hqE _
   _=(m:ENNReal)/((m:ENNReal)*2^t):=by rw [hcast]
   _=(m:ENNReal)*1/((m:ENNReal)*2^t):=by rw [mul_one]
   _=1/2^t:=ENNReal.mul_div_mul_left 1 (2^t) hm0 hmtop
end
end ProximityPrize.SubmissionLower.RCN284
end PackedLegacy_P1

end Compact_PackedLegacy


