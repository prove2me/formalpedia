-- Prove2me | Definitions.Def_Yukon_cfd2e7e9b4a5d9c97487b438
-- name    : Yukon_cfd2e7e9b4a5d9c97487b438
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T23:42:30.762889+00:00
-- url     : https://prove2.me/theorems/64dea0f4-1a1d-486c-aeb9-750f75819cb7
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceReducedGamma6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-5ffab05943aa804eb9ce13fb6fdd5f0835ca7bd35a44e5b53e3b9dce79be0a4c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjQxMjViMmNmN2QyNDgxZDA0NjNhOTVlMmIyZjdkYjU5OTU0NTAyYjNkYTI0MmQ0ZjIxZDVjOTE4NDVmZDA0MSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtNWZmYWIwNTk0M2FhODA0ZWI5Y2UxM2ZiNmZkZDVmMDgzNWNhN2JkMzVhNDRlNWI1M2UzYjlkY2U3OWJlMGE0YyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2NmZDJlN2U5YjRhNWQ5Yzk3NDg3YjQzOCIsInYiOjJ9]

import Definitions.Def_Yukon_1cd70c1313f8de4ca20c8ffd



import Definitions.Def_Yukon_1f886e14a1fc29f50d6a3d3c



















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Actual suppliers for the reduced cycle: old-prime membership,
properness, the small first-tail flag, and a separating gamma coordinate.
Only gamma's degree is compared to the characteristic. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN264 RCN313
open RCN002 RCN022 RCN037 RCN042 RCN093 RCN341
open MovingSourceFlowNumerator6814 MovingSourceReducedCycle6814
open MovingSourceProjectionFamily6814 MovingSourceAutomaticProjection6814
open MovingSourceLinearFlow6814 MovingSourceReducedRoutes6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

/-- Even old components contained in Hnew=0 occur in the new first cut.
They are not silently removed from the shared cycle. -/
theorem reducedTail_mem_old_component
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (C : FirstTailComponent S) : reducedTailSurface H G∈C.1 := by
  let ev := surfaceMap (polynomialEmbedding K)
  have hF : ev S.F∈C.1 := RCN312.firstTailComponent_surface_mem S C
  have hold : ev (numerator K S.F (RCN326.w+1))∈C.1 :=
    (RCN330.globalTailCut_mem_iff (polynomialEmbedding K) (polynomialEmbedding_injective K)
      S.F (RCN326.w+1) C.1).mp
      (regularComponent_T_mem (GenericField K) S.G _ _ C)
  have hc := C.1.mem_of_dvd (map_dvd ev hcross) hF
  simp only [map_sub,map_mul,map_pow] at hc
  have hm := C.1.sub_mem (C.1.mul_mem_left ((ev H)^(2*(RCN326.w+1))) hold) hc
  simp only [sub_sub_cancel] at hm
  have hprime : C.1.IsPrime := inferInstance
  have hOld : (ev (polyH K S.F))^(2*(RCN326.w+1))∉C.1 := by
    intro hh
    exact RCN312.firstTailComponent_regularity_not_mem S C
      (hprime.mem_of_pow_mem _ hh)
  exact (hprime.mem_or_mem hm).resolve_left hOld

/-- New properness follows from old properness and the only relevant
surface-level denominator exclusion. -/
theorem reducedTail_proper
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) H) : ¬S.G∣reducedTailSurface H G := by
  let ev := surfaceMap (polynomialEmbedding K)
  have hc := S.G_dvd_surface.trans (map_dvd ev hcross)
  simp only [map_sub,map_mul,map_pow] at hc
  intro hd
  change S.G∣ev (numerators H G (RCN326.w+1)) at hd
  have hprod := hc.add (dvd_mul_of_dvd_right hd ((ev (polyH K S.F))^(2*(RCN326.w+1))))
  rw [sub_add_cancel] at hprod
  have hpow : ¬S.G∣(ev H)^(2*(RCN326.w+1)) :=
    fun hh => hH (S.irreducible_G.prime.dvd_of_dvd_pow hh)
  have hraw := (S.irreducible_G.prime.dvd_or_dvd hprod).resolve_left hpow
  apply hfirst
  rw [globalTailCut_eq]
  exact dvd_mul_of_dvd_left hraw _

theorem surface_flag_of_caps
    {Ω : Type} [Field Ω] (phi : Polynomial K →+* Ω)
    (N : MvPolynomial (Fin 4) K) (B A C : ℕ) (hBA : B≤A) (hAC : A≤C)
    (hB : RCN234.wt RCN156.residualSWeights N≤B)
    (hA : RCN234.wt RCN156.residualYSWeights N≤A)
    (hC : RCN234.wt RCN156.residualTotalWeights N≤C) :
    PolynomialInFlag ⟨C-A,A-B,B⟩ (surfaceMap phi N) := by
  intro e he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset phi N he)
  have hb := (MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights hd).trans hB
  have ha := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd).trans hA
  have hc := (MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hd).trans hC
  rw [RCN081.weight_fin4] at hb ha hc
  simp [RCN156.residualSWeights,RCN156.residualYSWeights,RCN156.residualTotalWeights] at hb ha hc
  change d 2≤B ∧ d 1+d 2≤A-B+B ∧ d 1+d 2+d 3≤C-A+(A-B)+B
  omega

def reducedFirstFlag : FlagDegree := ⟨80216064,4849665,1441792⟩

theorem reducedFirstFlag_of_route
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute F J) :
    PolynomialInFlag reducedFirstFlag (reducedTailSurface (linearH J) (linearG J)) := by
  have hw := (hroute.2.2.2.2 (RCN326.w+1)).2
  exact surface_flag_of_caps (polynomialEmbedding K) _ 1441792 6291457 86507521
    (by decide) (by decide) hw.1 hw.2.1 hw.2.2

/-- Automatic separating parameter coordinate on the nonconstant-gamma
part of the original family. No Y- or R-projection degree gate is used. -/
theorem reduced_gamma_gate
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    (surfaceFlag tailFlag : FlagDegree)
    (hS : PolynomialInFlag surfaceFlag S.G)
    (hT : PolynomialInFlag tailFlag (reducedTailSurface H G))
    (hsmall : flagMixed surfaceFlag tailFlag unitZFlag<p)
    (C : FirstTailComponent S) : LiteralProjectionGate C 2 := by
  intro ht
  have ht' : Transcendental (GenericField K)
      (flagEvaluation (GenericField K) C.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))) := by
    simpa [Axis.order,RCN125.zOrder] using ht
  have he := RCN116.elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder])
  have hh := prime_projection_gate C.1 .z 0 0 0 ht' S.G (reducedTailSurface H G)
    S.irreducible_G.ne_zero (fun hz => hproper (hz ▸ dvd_zero _))
    (S.irreducible_G.isRelPrime_iff_not_dvd.mpr hproper)
    (regularComponent_G_mem (GenericField K) S.G _ _ C)
    (reducedTail_mem_old_component S H G hcross C) surfaceFlag tailFlag hS hT p hsmall
  rw [he] at hh
  exact hh

theorem checked_gamma_budget : flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitZFlag=140378124 ∧
    flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitZFlag<2130706433 := by decide +kernel









end
end ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814


