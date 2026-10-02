-- Prove2me | Definitions.Def_Yukon_2fad89a61572fab8c35498d6
-- name    : Yukon_2fad89a61572fab8c35498d6
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:19:30.434981+00:00
-- url     : https://prove2.me/theorems/0b7029c0-771c-49fe-b849-bded40828b94
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberProtocol6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberProtocol6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberProtocol6814.lean
--
--   yukon-proof-operation:foundation-direct-6ca13d044ed3c12a811b08e6e21b006e7c3b9b5b4568af1a653b2aa1dd99759c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODdlNmVlMDY0MDA1NDQ2ODJmMDA5NTdkNWI2Y2M5OWQ3YjQ5ODU1YzY2YTQ1YTQ0NTdhMmQxNzlmOTkyZmI0NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTZjYTEzZDA0NGVkM2MxMmE4MTFiMDhlNmUyMWIwMDZlN2MzYjliNWI0NTY4YWYxYTY1M2IyYWExZGQ5OTc1OWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yZmFkODlhNjE1NzJmYWI4YzM1NDk4ZDYiLCJ2IjoyfQ]

/- Private protocol instance, conditional on the new affine-line alignment theorem. -/
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561

import Definitions.Def_Yukon_f763b78685dab3987c5dbc33

























































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
section Compact_MovingFiberProtocol6814
/-! The exact 68.14 profile and its remaining proof obligation.
The scalar list arm, radius, score conversion and final extractor arithmetic
are checked here. The final theorem is conditional on AffineLineAlignmentBound;
the selected-count assembly must supply that final alignment bound. The proof template is adapted from
the promoted 68.3 LocatorProtocol and LocatorArithmetic modules. -/
namespace ProximityPrize.SubmissionLower.MovingFiberProtocol6814Arithmetic
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false
def errors : ℕ := 80889
def radiusNumerator:ℕ:=331325439
def radiusDenominator:ℕ:=1073741824
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
theorem radius_floor:
    ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors:=by
  norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    errors,IRSProfile.Index]
theorem radius_admissible:
    radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ)^14 * 100000000^100 ≤ 110190512^100:=by decide
theorem score_radius_integer:
    (742416385:ℕ)^128 * (2^68 * 110190512) ≤ 100000000 * 1073741824^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((14:ℝ)/100) ≤ (110190512:ℝ≥0)/100000000:=by
  have hroot:((2:ℝ≥0)^(14:ℕ))^((100:ℝ)⁻¹) ≤ (110190512:ℝ≥0)/100000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((14:ℝ)/100) = ((2:ℝ≥0)^(14:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(68:ℕ)) * (100000000/110190512):=by
  have hsub:(1 - radius:ℝ≥0) =742416385/1073741824:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(68:ℕ)) * (100000000/110190512)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6814:=by
  have hscale:(100000000:ℝ≥0)/110190512 ≤ (2:ℝ≥0)^(-((14:ℝ)/100)):=by
    calc
      (100000000:ℝ≥0)/110190512=1/((110190512:ℝ≥0)/100000000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((14:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(68:ℕ)) * (100000000/110190512):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(68:ℕ)) * (2:ℝ≥0)^(-((14:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6814:=by
      unfold claimedError
      rw [show -((((6814:ℕ):ℝ)/100)) =
          -((68:ℕ):ℝ) + -((14:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end ProximityPrize.SubmissionLower.MovingFiberProtocol6814Arithmetic

namespace ProximityPrize.SubmissionLower.MovingFiberProtocol6814
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000
local instance _root_.ProximityPrize.SubmissionLower.MovingFiberProtocol6814.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.MovingFiberProtocol6814.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
def n:ℕ:=262144
def errors:ℕ:=80889
def agreements:ℕ:=n-errors
def listBudget:ℕ:=8806647153
def mcaBudget:ℕ:=274980719304747934
def radius:ℝ≥0:=MovingFiberProtocol6814Arithmetic.radius
theorem sixteen_row_separation:
   15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field:=by
 rw [show Fintype.card IRSProfile.Field= (2130706433:ℕ) ^ 6 by
   norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
   Nat.choose_eq_descFactorial_div_factorial]
 norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem squared_eight_lambda_new
   (delta:ℝ)
   (hcell:(delta:ℝ) * (Fintype.card IRSProfile.Index:ℝ) <
     ((errors + 1:ℕ):ℝ)) :
   Code.Lambda
     (((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin 8 → IRSProfile.Field)) :
       Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
     delta ≤ (listBudget:ℕ∞):=by
 apply RCN280.squared_eight_lambda_le_of_interleaved_list
   IRSProfile.baseCode errors listBudget ?_ delta hcell
 intro received L hrows hclose
 have hclose':∀ v ∈ L,agreements ≤
     (Finset.univ.filter (fun i=> v i=received i)).card:=by
   intro v hv
   have hc : Fintype.card IRSProfile.Index = n := Fintype.card_fin _
   have he : n - errors = agreements := by decide +kernel
   have hh := hclose v hv
   rw [hc, he] at hh
   exact hh
 classical
 letI:DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩ :=
   Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
 have hsepD:15 * D.card.choose 2 < Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact sixteen_row_separation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (IRSProfile.Index → IRSProfile.Field) :=
   D.image (momentProjection (ι:=IRSProfile.Index) (r:=16) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c ∈ projected,c ∈ IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀ c ∈ projected,agreements ≤
     (Finset.univ.filter (fun i=> c i=momentProjection t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose' v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v received))
 have hbound:=MovingFiberScalarList6814.irs_scalar_finite_list_card_le
   (momentProjection t received) projected hcode hnear
 change projected.card ≤ listBudget at hbound
 rw [hprojcard,hDcard] at hbound
 omega
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code ^⋈ (Fin 2) :
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (radius:ℝ) ≤ (listBudget:ℕ∞):=by
 rw [irs_squared_carrier_eq]
 apply squared_eight_lambda_new (radius:ℝ)
 norm_num [radius,MovingFiberProtocol6814Arithmetic.radius,claimedRadius,
   MovingFiberProtocol6814Arithmetic.radiusNumerator,
   MovingFiberProtocol6814Arithmetic.radiusDenominator,
   errors,IRSProfile.Index]
theorem base_mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ) ≤
     ENNReal.ofReal ((mcaBudget:ℝ) / Fintype.card IRSProfile.Field):=by
 apply mcaError_affineLine_le_of_givenSetsBound
 apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors by
     simpa only [radius,errors,MovingFiberProtocol6814Arithmetic.errors] using
       MovingFiberProtocol6814Arithmetic.radius_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,MovingFiberProtocol6814Arithmetic.errors] at hcomp ⊢
   omega
 · exact halign
theorem mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ) ≤
     (mcaBudget:ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [RCN284.irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,MovingFiberProtocol6814Arithmetic.radius,
         claimedRadius,MovingFiberProtocol6814Arithmetic.radiusNumerator,
         MovingFiberProtocol6814Arithmetic.radiusDenominator])
       (by norm_num [radius,MovingFiberProtocol6814Arithmetic.radius,
         claimedRadius,MovingFiberProtocol6814Arithmetic.radiusNumerator,
         MovingFiberProtocol6814Arithmetic.radiusDenominator])
   _ ≤ ENNReal.ofReal
       ((mcaBudget:ℝ) / Fintype.card IRSProfile.Field) :=
     base_mca_le_of_alignment halign
   _= (mcaBudget:ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem field_capacity_split:
   2 ^ (128:ℕ) * (mcaBudget + listBudget) ≤
     Fintype.card IRSProfile.Field:=by
 rw [RCN284.field_cardinality]
 norm_num [mcaBudget,listBudget]
theorem certifiedGammaError_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   certifiedGammaError IRSProfile.code radius ≤
     (1:ℝ≥0) / 2 ^ (128:ℕ):=by
 rw [← ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code ^⋈ (Fin 2) :
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
         Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) ≤
       (listBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) :=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _ ≤ (mcaBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) +
       (listBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) :=
     add_le_add (mca_le_of_alignment halign) hList
   _= ((mcaBudget + listBudget:ℕ):ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [← ENNReal.add_div,Nat.cast_add]
   _ ≤ (1:ENNReal) / 2 ^ (128:ℕ):=by
     apply RCN284.nat_div_le_inv_pow
     · norm_num [mcaBudget,listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6814_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   ProtocolClaim 6814 331325439 1073741824 where
 admissible:=MovingFiberProtocol6814Arithmetic.radius_admissible
 reduction:=by
   change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
   simpa [reductionTarget,ProximityGap.prizeThreshold] using
     certifiedGammaError_le_of_alignment halign
 score:=by
   change (1 - MovingFiberProtocol6814Arithmetic.radius) ^
     IRSProfile.repetitions ≤ claimedError 6814
   exact MovingFiberProtocol6814Arithmetic.score_target_le
end
end ProximityPrize.SubmissionLower.MovingFiberProtocol6814

end Compact_MovingFiberProtocol6814

section Compact_Protocol80850
/-! Reuse the checked scalar-list reduction and 68.14 score arithmetic at
this exact radius. The new work supplies its alignment hypothesis. -/
namespace ProximityPrize.SubmissionLower.Lower80860.Protocol
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280

end ProximityPrize.SubmissionLower.Lower80860.Protocol

end Compact_Protocol80850


