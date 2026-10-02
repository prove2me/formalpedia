-- Prove2me | Definitions.Def_Yukon_964429eea3e1d9a3c2850a3a
-- name    : Yukon_964429eea3e1d9a3c2850a3a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:30:47.49908+00:00
-- url     : https://prove2.me/theorems/190f05fd-5387-4e0c-bb50-02ae47f16c41
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeRectangleCount6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeRectangleCount6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeRectangleCount6814.lean
--
--   yukon-proof-operation:foundation-direct-7a5751454df0523aa831137c347469fd2551dc42ecf392445e9d114bd41a3634
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNmY3ZTRmODkxNmIxMDY2NDYxMzU5MDNmNDcxNTE1Y2U0ODFkOTUzNDI5Yzc1ZjJiZjUyODQ1MTk4ZThjZmRmMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTdhNTc1MTQ1NGRmMDUyM2FhODMxMTM3YzM0NzQ2OWZkMjU1MWRjNDJlY2YzOTI0NDVlOWQxMTRiZDQxYTM2MzQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85NjQ0MjllZWEzZTFkOWEzYzI4NTBhM2EiLCJ2IjoyfQ]

import Definitions.Def_Yukon_acb5a197f811d10dcf0b8b9d












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! A checked rectangle supplies the actual proper helper and the
regular-seed count, including its unbounded upper-weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 RelativeBounded6814 ContactOrderBridge
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

def pair (b : Band) (d : Rectangle) : UnequalParameters :=
  ⟨262144,131071,181255,b.B,b.R,b.T1,d.U,d.s,max d.L0 d.L1⟩

def Valid (b : Band) (d : Rectangle) : Prop :=
  Shape b d ∧ 1≤b.R ∧ b.B<2130706433 ∧ b.R<2130706433 ∧ b.T1<2130706433 ∧
  cutoff b d≤131071*(d.U+1) ∧
  (pair b d).mixedCost.y<2130706433 ∧ (pair b d).mixedCost.r<2130706433 ∧
  (pair b d).mixedCost.z<2130706433 ∧
  AsymmetricHelper.leftRegularCountCap (pair b d)≤b.count ∧
  checkRows b d (b.B+b.R+1)=true

instance validDecidable (b : Band) (d : Rectangle) : Decidable (Valid b d) := by
  unfold Valid
  infer_instance

theorem cutoff_of_clipped_weight (b : Band) (d : Rectangle) (nu : ℕ)
    (hhi : min nu (tail b)≤d.hi) :
    cutoff b d≤d.alpha*181255-d.beta*min (nu-131071+1) ((b.B+b.R-1)*181255) := by
  unfold cutoff
  apply Nat.sub_le_sub_left
  apply Nat.mul_le_mul_left
  by_cases hn : nu≤tail b
  · have hh : nu≤d.hi := by simpa only [min_eq_left hn] using hhi
    exact min_le_min (by omega) le_rfl
  · have hh : tail b≤d.hi := by simpa only [min_eq_right (by omega : tail b≤nu)] using hhi
    have hc : (b.B+b.R-1)*181255≤d.hi-131071+1 := by unfold tail at hh; omega
    rw [min_eq_right hc]
    exact min_le_right _ _

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertificate6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count_of_rectangle (b : Band) (d : Rectangle) (hvalid : Valid b d)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hlo : d.lo≤nu) (hhi : min nu (tail b)≤d.hi)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  classical
  rcases hvalid with ⟨hshape,hRpos,hBchar,hRchar,hTchar,hU,hgY,hgR,hgZ,hprice,hcheck⟩
  have hF := RCN167.positiveRFactors_spec H F.val F.property
  let Delta := RCN140.regularSeeds H selected Gamma F
  have hsub : Delta⊆Gamma := RCN140.regularSeeds_subset H selected Gamma F
  have hsol : ∀ gamma∈Delta, specialization K (selected gamma) gamma F.val=0 := by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.1
  have hreg : ∀ gamma∈Delta, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F.val)≠0 := by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.2
  have hrows := rectangle_rows b d T hshape hT0 hT1 hcheck
  have hlower := total_lower b d T hshape hT0 hT1
  have hupper := total_upper b d T hshape hT0 hT1
  have hshape' := hshape
  rcases hshape' with ⟨_,hRs,_,hweight,_,_,hD,_,_,_,_⟩
  have hTL : T≤total b d T := by
    have hh := (max_le_iff.mp hlower).1
    dsimp [lowerTotal] at hlower
    omega
  have hrowsNu := profile_rows_mono_weight (D:=cutoff b d) (w:=131071) (L:=total b d T)
    (s:=d.s) (T:=T) (R:=b.R) (B:=b.B) (N:=262144) (alpha:=d.alpha) (beta:=d.beta) hlo hrows
  obtain ⟨Q,hQ,hrel,hzero⟩ := exists_profile_helper K
    (D:=cutoff b d) (L:=total b d T) (s:=d.s) (nu:=nu) (B:=b.B)
    F.val hF.1 hF.2.2 hbox hTL hRs hcode htotal hslope hB nodes u0 u1 d.alpha d.beta 181255
    (by omega) hD (cutoff_of_clipped_weight b d nu hhi)
    (by simpa only [hcard] using hrowsNu)
    selected Delta (fun gamma hg => hdegree gamma (hsub hg)) hsol hreg
    (fun gamma hg => hagreement gamma (hsub hg))
  have hFY : F.val.degreeOf 1≤b.B := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights he).trans hB
    rw [RCN081.weight_fin4] at hw
    simp [RCN156.residualYSWeights] at hw
    omega
  have hFR : F.val.degreeOf 2≤b.R := MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hbox he).2.1)
  have hFZ : F.val.degreeOf 3≤b.T1 := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hbox he).1; omega)
  have hQY : Q.degreeOf 1≤d.U := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hQ he).2.2; omega)
  have hQR : Q.degreeOf 2≤d.s := MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hQ he).2.1)
  have hQZ : Q.degreeOf 3≤max d.L0 d.L1 := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hQ he).1; omega)
  apply le_trans ?_ hprice
  exact AsymmetricHelper.regularSeeds_count_le_left_intersection
    (pair b d) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    hRpos hBchar hRchar hTchar hgY hgR hgZ
    selected Gamma (Finset.univ : Finset I) nodes u0 u1 nodes.injective.injOn
    (by simpa only [pair,Finset.card_univ] using hcard)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    hdegree hagreement (by simpa only [pair,UnequalParameters.errors,Nat.reduceSub] using hno) hzero



end
end ProximityPrize.SubmissionLower.RelativeCertificate6814


