-- Prove2me | Definitions.Def_Yukon_28be9ec982818aa5b286d017
-- name    : Yukon_28be9ec982818aa5b286d017
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:10:22.338912+00:00
-- url     : https://prove2.me/theorems/0da0f757-e1ea-4be5-873a-cf1ef63a0808
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailProjection.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailProjection.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailProjection.lean
--
--   yukon-proof-operation:foundation-direct-0e11ac796778633ee2147236abe4d4076b204874d6b3626da4204466ab47152f-parser-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNWMzNTJiM2QwNjM4MmYzOWFhMWVlOWYyZjRlNzhhMzVmY2QwNGUyOWNkYmYwZGE5ZDA4NjExZjY3OGQwZWRiYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTBlMTFhYzc5Njc3ODYzM2VlMjE0NzIzNmFiZTRkNDA3NmIyMDQ4NzRkNmIzNjI2ZGE0MjA0NDY2YWI0NzE1MmYtcGFyc2VyLXJldHJ5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMjhiZTllYzk4MjgxOGFhNWIyODZkMDE3IiwidiI6Mn0]

import Definitions.Def_Yukon_1dcaba27524a91653739dbc3












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailProjection
open scoped Classical BigOperators
open BoundaryTailSharpGate
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+* Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance _root_.ProximityPrize.SubmissionLower.BoundaryTailProjection.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.BoundaryTailProjection.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.BoundaryTailProjection.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
theorem exists_reduced_firstTail_activeNestedData_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < pchar) :
   ∃ (base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F), SeparableLiteralCoordinate C.1),
     ∃ (hactive:∀ C:RegularComponent Omega S.G
         (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
         (regularitySurface phi S.F),
         KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0 ∨
           KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃ (hZ:∀ C:RegularComponent Omega S.G
           (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
           (regularitySurface phi S.F), LiteralProjectionGate C 2),
         Nonempty (AdaptiveNestedProjectionDataActive base hactive
           (RCN315.residualStage_pderiv_one_ne_zero_of_support S)):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T, Tred, sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY, hGS, hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 have hGdegree:∀ j:Fin 3, S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR := RCN315.residualStage_pderiv_one_ne_zero_of_support S
 let hZ:∀ C:RegularComponent Omega S.G Tred H, LiteralProjectionGate C 2 := by
   intro C htr
   exact finite_separable_z_of_flag_gate C.1 htr pchar S.G Tred
     S.irreducible_G (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C) hproperRed hR
     flag (reducedResidualAgreementFlag supp (w+1)) hGflag hTflag hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 := by
   intro C
   by_cases hz:Transcendental Omega (coordinate Omega C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy := (regularComponent_y_or_z_transcendental phi S.F S.G Tred
       S.G_dvd_surface C).resolve_right hz
     have hsep := finite_separable_at_y_of_z_algebraic C.1 pchar S.G
       S.irreducible_G (regularComponent_G_mem Omega S.G Tred H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 exact ⟨base, hactive, hZ,
   exists_adaptiveNestedProjectionDataActive base hactive
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.BoundaryTailProjection

namespace ProximityPrize.SubmissionLower.BoundaryTailProjection
open scoped Classical BigOperators
open BoundaryTailSharpGate
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
   (hmixed:flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag < p):
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
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR := RCN315.residualStage_pderiv_one_ne_zero_of_support S
 let hZ:∀ C:RegularComponent Ω S.G T H, LiteralProjectionGate C 2 := by
   intro C htr
   exact finite_separable_z_of_flag_gate C.1 htr p S.G T
     S.irreducible_G (regularComponent_G_mem Ω S.G T H C)
     (regularComponent_T_mem Ω S.G T H C) hproper hR
     flag (sharpResidualAgreementFlag (support a b s) w) S.flag_support hTflag hmixed
 let choiceData:∀ C:RegularComponent Ω S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 := by
   intro C
   by_cases hz:Transcendental Ω (coordinate Ω C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy := (regularComponent_y_or_z_transcendental φ S.F S.G T
       S.G_dvd_surface C).resolve_right hz
     have hsep := finite_separable_at_y_of_z_algebraic C.1 p S.G
       S.irreducible_G (regularComponent_G_mem Ω S.G T H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
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
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end ProximityPrize.SubmissionLower.BoundaryTailProjection


