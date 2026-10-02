-- Prove2me | Definitions.Def_Yukon_ee9864870dbf5e55a5c9c20a
-- name    : Yukon_ee9864870dbf5e55a5c9c20a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:49:02.789627+00:00
-- url     : https://prove2.me/theorems/02c072e7-ad94-48b2-bfbb-8066f900493c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberOrdinaryHigh6814.lean
--
--   yukon-proof-operation:foundation-direct-26b2666ceac12b7e7e5551391eded51fbd256fa0a4152d99674a807c2e0e2af3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTE5NWQwYzkwZjM4ZDMyYTNlYWVmZDA3ODNkNzQyZDQ2OTEwYjcyN2FmNWUxNmQ3ODcxMzdlNWUyYzhhNGEwMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTI2YjI2NjZjZWFjMTJiN2U3ZTU1NTEzOTFlZGVkNTFmYmQyNTZmYTBhNDE1MmQ5OTY3NGE4MDdjMmUwZTJhZjMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lZTk4NjQ4NzBkYmY1ZTU1YTVjOWMyMGEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_60a3ec8beeda1bdba065048d

import Definitions.Def_Yukon_c5963d87513e7df48d813483

import Definitions.Def_Yukon_8e36628a28757c81c2b971d7

import Definitions.Def_Yukon_b41d2bba81933bb0509ee1b5


















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814

open scoped Classical BigOperators
open RCN135 RCN136 RCN139 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095
open RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312
open RCN339 RCN330 RCN174 RCN319 RCN206 RCN287 RCN066 RCN338 RCN199 RCN207
open RCN271 RCN313 RCN234 RCN156 RCN341 RCN085 RCN149 RCN087 RCN203 RCN084 RCN335
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def bound (flag : FlagDegree) (t y r : ℕ) : ℕ :=
  flagMixed flag (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r) +
    65539 * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)

theorem bound_eq_abs (flag : FlagDegree) (t y r : ℕ)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) :
    bound flag t y r = BoundaryTailIdentityArithmetic.newCost flag
      (cellA t y) (cellB y r) (cellS r) := by
  have hfirst := SecondJetIdentity.cell_first_eq t y r
  have hnormal : BoundaryTailProvider.cellNormal t y r =
      Lower80788.HybridIdentityC2.rationalABS (cellA t y) (cellB y r) (cellS r) +
        131071 • unitAllFlag := by
    unfold BoundaryTailProvider.cellNormal
    rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hb,
      SecondJetIdentity.cell_normal_eq]
    rfl
  have hfiber : cellMovingFiber t y r =
      Lower80788.HybridIdentityC2.mfibABS (cellA t y) (cellB y r) (cellS r) := rfl
  have hrat : cellRational t y r =
      Lower80788.HybridIdentityC2.rationalABS (cellA t y) (cellB y r) (cellS r) :=
    SecondJetIdentity.cell_normal_eq t y r
  have hcut : cellMovingCut t y r =
      Lower80788.HybridIdentityC2.mcutABS (cellA t y) (cellB y r) (cellS r) := by
    simp only [cellMovingCut, Lower80788.HybridIdentityC2.mcutABS, hrat,
      RCN327.w, Nat.reduceAdd, Nat.reduceMul]
  unfold bound BoundaryTailIdentityArithmetic.newCost BoundaryTailIdentityArithmetic.newNormal
  rw [hfirst, hnormal, hfiber, hcut]

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

/-- The actual ordinary high-cell count at 80889 errors, including the
identity-first-tail branch. No positive Z-degree assumption is used. -/
theorem stage_card_le (D t y r : ℕ)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (hRcap : r ≤ 32) (hYcap : y ≤ 149) (hTcap : t ≤ 8121)
    (hSafe : BoundaryTailGates6808.Safe r y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80889 flag
      w (cellSupport t y r))
    (hnodes : S.nodes.card = 181255+80889)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧
      flag.zOnly+flag.yz+flag.all ≤ t) :
    Gamma.card ≤ bound flag t y r := by
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  have hshort : w+1 ≤ D := by simpa only [RCN327.w] using hDlow
  have hb1 : 1 ≤ cellB y r := by dsimp [cellB]; omega
  have hs1 : 1 ≤ cellS r := by dsimp [cellS]; omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w+1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hidentityGate := BoundaryTailGates6808.identity_gate flag t y r hSafe hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider
      (a := cellA t y) (b := cellB y r) (s := cellS r) S 181255 hnodes hagreement
      (by norm_num [RCN327.w]) hTailNumerator D t r
      (by norm_num [RCN327.w]) hshort hDchar hbox hflagChar hidentityGate
    have hpositive : 1 ≤ ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r)
        (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181255
      (ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w)
      hprovider hagreement (by norm_num [RCN327.w])
      (by rw [hnodes]; norm_num [RCN327.w]) hpositive
    have habsorb := MovingFiberIdentityArithmetic6814.generic_absorption flag
      (cellA t y) (cellB y r) (cellS r) (Nat.zero_le _) hb1 hs1
    have hscaled : Gamma.card * 50184 ≤ 50184 * bound flag t y r := by
      calc
        Gamma.card * 50184 = Gamma.card * (181255-w) := by norm_num [RCN327.w]
        _ ≤ (S.nodes.card-w) * (80889+1) *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := hinc
        _ = 131073 * 80890 *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) 131071 := by
          rw [hnodes]
          norm_num [RCN327.w]
        _ ≤ 50184 * BoundaryTailIdentityArithmetic.newCost flag
            (cellA t y) (cellB y r) (cellS r) := habsorb
        _ = 50184 * bound flag t y r := by rw [bound_eq_abs flag t y r hr3 hb]
    apply Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < 50184)
    simpa only [Nat.mul_comm] using hscaled
  · have hmixedRed := BoundaryTailGates6808.reduced_gate flag t y r hSafe hflag.1 hflag.2.1
    have hmix : 2 * (flag.zOnly+flag.yz+flag.all) *
        (cellA t y+cellB y r+cellS r+4) < 2130706433 := by
      have hf : flag.zOnly+flag.yz+flag.all ≤ 8121 := hflag.2.2.trans hTcap
      have ht : cellA t y+cellB y r+cellS r+4 ≤ 8122 := by
        dsimp [cellA, cellB, cellS]
        omega
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf) ht).trans_lt (by decide)
    have hrationalGate : 80889+1 ≤ (BoundaryTailProvider.cellNormal t y r).yz := by
      have hv : 2 ≤ y-r := by omega
      simp only [BoundaryTailProvider.cellNormal, BoundaryTailAlgebra.normalFlag, RCN327.w]
      omega
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (80889+1) *
              (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail
        (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixedRed C)
        181255 D t r hnodes hagreement
        (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) hshort hDchar hbox
        (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C)
        hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
    obtain ⟨provider⟩ := BoundaryTailRealization.exists_provider hr3 hb hyt
      (by norm_num [RCN327.w]) S hTail hflagChar hmixedRed hmix hrationalGate htangent
    exact stage_card_le_divisorBound S provider

end
end ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6814


