-- Prove2me | Definitions.Def_Yukon_585a84ad2d6a66e7122d7d84
-- name    : Yukon_585a84ad2d6a66e7122d7d84
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T20:41:34.328286+00:00
-- url     : https://prove2.me/theorems/a952b213-1bf0-4730-9ec6-108d3222a5ff
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmeticBase6814.lean
--
--   yukon-proof-operation:certificate-split-0d6287a208eb03175bc02c8ea0ba8bc7c25e7448670d321916c4acd2733e374a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTc3Zjc4YWJlYWI0M2QwODI4N2M4OWZkMzM1MTYwMTdkYTBmNDI4NTQ1ZWQ3N2E5MmMwZDBkOTRiM2E4ZDU0NCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTBkNjI4N2EyMDhlYjAzMTc1YmMwMmM4ZWEwYmE4YmM3YzI1ZTc0NDg2NzBkMzIxOTE2YzRhY2QyNzMzZTM3NGEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81ODVhODRhZDJkNmE2NmU3MTIyZDdkODQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_b1c9b4d9cea8738703f9c7ae





















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6814
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 LocatorHybridCells LocatorHybridCellsC1
open MovingFiberProfile6814 MovingFiberThreeSources6811 MovingFiberRegularData6814
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def first (a b c : ℕ) : FlagDegree := ⟨262144*c,262144*b+524288,262144*a+524291⟩
def normal (a b c : ℕ) : FlagDegree := ⟨131074*c,131074*b+131076,131074*a+262148⟩
def raw (a b c : ℕ) : FlagDegree := ⟨131073*c,131073*b+262146,131073*a+393218⟩
def graph (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) : ℕ :=
  scale/3*flagMixed f (first a b c) (normal a b c) +
    ∑ j : Fin 3, (524288*weight (normal a b c) j*(scale/(3*(cfg j).d))+
      65539*weight (raw a b c) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag
def identityDegree (p : FlagDegree) (a b c : ℕ) : ℕ :=
  p.zOnly*(655365+262146*a)+p.yz*(1310730+524292*a)+
    p.all*(2097170+524292*a+524292*b+262146*c)
def pairNumerator (a b c capY capR capT : ℕ) : ℕ :=
  131073*((1+262142*(a+b+5))*((a+3)*capT+(a+b+c+5)*capR)+
    131071*(2*a+5)*((a+b+5)*capT+(a+b+c+5)*capY)+
    (1+262142*(a+b+c+5))*((a+b+5)*capR+(a+3)*capY))+
    80890*50184*((a+b+5)*capR+(a+3)*capY)
def coeff (P : Params) (a b c : ℕ) : ℕ := pairNumerator a b c P.U P.B P.L
def helper (P : Params) (a b c : ℕ) : ℕ :=
  pairNumerator a b c (P.U+P.s*(a+b+4)) (P.B+P.s*(a+2)) (P.L+P.s*(a+b+c+4))

theorem number_coordinates (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) :
    number cfg scale (a+3+(b+2)+c) (a+3+(b+2)) (a+3) f = graph cfg scale f a b c := by
  have hy : a+3+(b+2)-(a+3) = b+2 := by omega
  have hz : a+3+(b+2)+c-(a+3+(b+2)) = c := by omega
  have hr2 : a+3-2 = a+1 := by omega
  have hb : b+2-1 = b+1 := by omega
  have hv2 : 131074*(b+2)-131072 = 131074*b+131076 := by omega
  have hfirst : MovingFiberRetainedStage6811.hfreeFirst (a+3+(b+2)+c) (a+3+(b+2)) (a+3) =
      first a b c := by
    have h : a+3-1 = a+2 := by omega
    unfold MovingFiberRetainedStage6811.hfreeFirst HFreeFirstSlice6812.hfreeFlag first unitAllFlag
    rw [hy,hz,h]
    show FlagDegree.mk (2*(RCN326.w+1)*c+3*0) (2*(RCN326.w+1)*(b+2)+3*0)
      (2*(RCN326.w+1)*(a+2)+3*1) = _
    rw [FlagDegree.mk.injEq,show RCN326.w = 131071 from rfl]
    exact ⟨by ring,by ring,by ring⟩
  have hn : BoundaryTailProvider.cellNormal (a+3+(b+2)+c) (a+3+(b+2)) (a+3) = normal a b c := by
    norm_num only [BoundaryTailProvider.cellNormal,BoundaryTailAlgebra.normalFlag,normal,w,hy,hz,hv2,
      FlagDegree.mk.injEq,true_and]
    omega
  have hraw : MovingFiberRetainedStage6811.rawFirstFlag (a+3+(b+2)+c) (a+3+(b+2)) (a+3) = raw a b c := by
    simp only [MovingFiberRetainedStage6811.rawFirstFlag,cellA,cellB,cellS,hz,hy,hb,hr2,
      RCN198.center,RCN198.direction,raw,w,unitYZFlag]
    change FlagDegree.mk (0+2*c+131071*c) (1+(2*(b+1)+1)+131071*(b+1+1))
      (0+(2*(a+1)+3)+131071*(a+1+2)) = _
    have e0 : 0+2*c+131071*c=131073*c := by ring
    have e1 : 1+(2*(b+1)+1)+131071*(b+1+1)=131073*b+262146 := by ring
    have e2 : 0+(2*(a+1)+3)+131071*(a+1+2)=131073*a+393218 := by ring
    rw [e0,e1,e2]
  have hw4 : 4*(w+1) = 524288 := rfl
  simp only [number,graph,hfirst,hn,hraw,hw4]

theorem identity_coordinates (f : FlagDegree) (a b c : ℕ) :
    identityCurveDegree f (cellA (a+3+(b+2)+c) (a+3+(b+2)))
      (cellB (a+3+(b+2)) (a+3)) (cellS (a+3)) w = identityDegree f a b c := by
  change identityCurveDegree f _ _ _ Lower80788.HybridIdentityC2.w = _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  have ha : cellA (a+3+(b+2)+c) (a+3+(b+2)) = c := by dsimp [cellA]; omega
  have hb : cellB (a+3+(b+2)) (a+3) = b+1 := by dsimp [cellB]; omega
  have hs : cellS (a+3) = a+1 := by dsimp [cellS]; omega
  rw [ha,hb,hs]
  simp only [identityDegree]
  ring

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem pair_numerator (S : Data nodes u0 u1) (a b c : ℕ)
    (hr : S.r=a+3) (hy : S.y=a+3+(b+2)) (ht : S.t=a+3+(b+2)+c) (R U T : ℕ) :
    AsymmetricHelper.leftRegularNumerator (S.pair R U T) = pairNumerator a b c U R T := by
  have hR : 2*(a+3)-1=2*a+5 := by omega
  norm_num only [Data.pair,AsymmetricHelper.leftRegularNumerator,UnequalParameters.errors,
    UnequalParameters.gap,UnequalParameters.leftAgreement,UnequalParameters.mixedCost,dot,hr,hy,ht,hR,pairNumerator]
  ring

theorem uniform_gates (S : Data nodes u0 u1) (R U T : ℕ)
    (hR : R ≤ 1284) (hU : U ≤ 5898) (hT : T ≤ 303449) : S.PairGates R U T := by
  have hr := S.rbound
  have hy := S.ybound
  have ht := S.tbound
  have hm : (S.pair R U T).mixedCost.y ≤ 31*303449+7501*1284 ∧
      (S.pair R U T).mixedCost.r ≤ 142*303449+7501*5898 ∧
      (S.pair R U T).mixedCost.z ≤ 142*1284+31*5898 := by
    dsimp [Data.pair,UnequalParameters.mixedCost]
    constructor
    · exact Nat.add_le_add (Nat.mul_le_mul hr hT) (Nat.mul_le_mul ht hR)
    constructor
    · exact Nat.add_le_add (Nat.mul_le_mul hy hT) (Nat.mul_le_mul ht hU)
    · exact Nat.add_le_add (Nat.mul_le_mul hy hR) (Nat.mul_le_mul hr hU)
  exact ⟨hm.1.trans_lt (by decide),hm.2.1.trans_lt (by decide),hm.2.2.trans_lt (by decide)⟩

theorem catalog_gates (S : Data nodes u0 u1) (g : Fin 21) (j : Fin 3) :
    let P := MovingFiberCatalog6814.groups g j
    S.PairGates (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)) ∧
    S.PairGates P.B P.U P.L := by
  dsimp only
  have hp := MovingFiberCatalog6814.common_caps g j
  have hr : S.r-1 ≤ 30 := by have := S.rbound; omega
  have hy : S.y-1 ≤ 141 := by have := S.ybound; omega
  have ht : S.t-1 ≤ 7500 := by have := S.tbound; omega
  constructor
  · apply uniform_gates
    · calc _ ≤ 84+40*30 := by gcongr; exact hp.1; exact hp.2.2.2
           _ ≤ 1284 := by decide
    · calc _ ≤ 258+40*141 := by gcongr; exact hp.2.1; exact hp.2.2.2
           _ ≤ 5898 := by decide
    · calc _ ≤ 3449+40*7500 := by gcongr; exact hp.2.2.1; exact hp.2.2.2
           _ ≤ 303449 := by decide
  · exact uniform_gates S _ _ _ (by omega) (by omega) (by omega)

def Own (S : Data nodes u0 u1) : Prop :=
  RCN130.originalCumulativeFlag S.F = ⟨S.t-S.y,S.y-S.r,S.r⟩

theorem own_total (S : Data nodes u0 u1) (hown : Own S) : RCN234.wt RCN156.residualTotalWeights S.F=S.t := by
  have h := (RCN130.originalCumulativeFlag_cumulative S.F).2.2
  rw [hown] at h
  have := S.ry
  have := S.yt
  dsimp only at h
  omega



end ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6814


