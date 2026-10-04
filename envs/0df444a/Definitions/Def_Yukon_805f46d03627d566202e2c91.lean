-- Prove2me | Definitions.Def_Yukon_805f46d03627d566202e2c91
-- name    : Yukon_805f46d03627d566202e2c91
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T21:13:59.78038+00:00
-- url     : https://prove2.me/theorems/3be2485b-c259-4201-ac76-743d4ec26e80
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeDirArith6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeDirArith6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeDirArith6814.lean
--
--   yukon-proof-operation:certificate-split-ec26508373963e8ada6b2ea21aed1e3e2603eca790074d69b73b6806243789d0
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzg0NWM1MzhmMjg0MDliNGVjMWMyNGM0NDExZDYwYjIzMmIxMjVkY2IzZWY0MDVkNTkzNjlmYmNlMDlmYjQ2ZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWVjMjY1MDgzNzM5NjNlOGFkYTZiMmVhMjFhZWQxZTNlMjYwM2VjYTc5MDA3NGQ2OWI3M2I2ODA2MjQzNzg5ZDAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84MDVmNDZkMDM2MjdkNTY2MjAyZTJjOTEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_585a84ad2d6a66e7122d7d84

import Definitions.Def_Yukon_276324f8991705e837e0a46f








































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# Per-direction H-free first cut: the arithmetic interface

The catalog form of `HFreeDir6813.numeratorDir`, for the generated receipts.  With
`r = a+3`, `v = b+2`, `z = c`:

* `numberDir` is `numeratorDir` over catalog parameters (`MovingFiberProfile6814.number`
  with the per-direction first cut), and `numberDir_coordinates` turns it into `graphDir`;
* `firstDir j a b c` is the first flag of direction `j`; it is polynomial on each of the regimes
  `r = 3` (`firstLo`) and `r ≥ 4` (`firstHi`, in `a-1`);
* `graphDir ≤ graph`, so the shipped receipts also cover `graphDir`.
-/

namespace ProximityPrize.SubmissionLower.HFreeDirArith6814
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 LocatorHybridCells LocatorHybridCellsC1
open MovingFiberProfile6814 MovingFiberThreeSources6811 MovingFiberRegularData6814
open MovingFiberArithmeticBase6814
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- `MovingFiberProfile6814.number` with the per-direction first cut; it is
`HFreeDir6813.numeratorDir` of the catalog sources. -/
def numberDir (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  ∑ j : Fin 3, (scale/3*weight (BoundaryTailProvider.cellNormal t y r) j*
      flagMixed f (HFreeDir6813.hfreeFirstDir t y r j) (direction j) +
    (4*(w+1)*weight (BoundaryTailProvider.cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

/-- The first flag of direction `j` at `r = a+3`, `v = b+2`, `z = c`. -/
def firstDir (j : Fin 3) (a b c : ℕ) : FlagDegree :=
  HFreeDir6813.hfreeFirstDir (a+3+(b+2)+c) (a+3+(b+2)) (a+3) j

/-- `firstDir` at `r = 3`. -/
def firstLo (j : Fin 3) (b c : ℕ) : FlagDegree :=
  ![⟨262144*c, 262144*b, 3⟩, ⟨262144*c, 262144*b+393216, 3⟩,
    ⟨262144*c, 262144*b+131072, 262147⟩] j

/-- `firstDir` at `r = a+4`. -/
def firstHi (j : Fin 3) (a b c : ℕ) : FlagDegree :=
  ![⟨262144*c, 262144*b+131072, 262144*a+131075⟩, ⟨262144*c, 262144*b+524288, 262144*a+131075⟩,
    ⟨262144*c, 262144*b+131072, 262144*a+524291⟩] j

theorem firstDir_zero (j : Fin 3) (b c : ℕ) : firstDir j 0 b c = firstLo j b c := by
  rw [HFreeDir6813.flag_eq_iff]
  fin_cases j <;>
    simp [firstDir, firstLo, HFreeDir6813.hfreeFirstDir, HFreeDir6813.hfreeFlagDir,
      HFreeDir6813.cuspFlag, unitAllFlag, RCN326.w] <;> omega

theorem firstDir_succ (j : Fin 3) (a b c : ℕ) : firstDir j (a+1) b c = firstHi j a b c := by
  rw [HFreeDir6813.flag_eq_iff]
  fin_cases j <;>
    simp [firstDir, firstHi, HFreeDir6813.hfreeFirstDir, HFreeDir6813.hfreeFlagDir,
      HFreeDir6813.cuspFlag, unitAllFlag, RCN326.w] <;> omega

/-- `graph` with the per-direction first cut. -/
def graphDir (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) : ℕ :=
  ∑ j : Fin 3, (scale/3*weight (normal a b c) j*flagMixed f (firstDir j a b c) (direction j) +
    (524288*weight (normal a b c) j*(scale/(3*(cfg j).d))+
      65539*weight (raw a b c) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

theorem numberDir_coordinates (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) :
    numberDir cfg scale (a+3+(b+2)+c) (a+3+(b+2)) (a+3) f = graphDir cfg scale f a b c := by
  have hy : a+3+(b+2)-(a+3) = b+2 := by omega
  have hz : a+3+(b+2)+c-(a+3+(b+2)) = c := by omega
  have hr2 : a+3-2 = a+1 := by omega
  have hb : b+2-1 = b+1 := by omega
  have hv2 : 131074*(b+2)-131072 = 131074*b+131076 := by omega
  have hn : BoundaryTailProvider.cellNormal (a+3+(b+2)+c) (a+3+(b+2)) (a+3) = normal a b c := by
    norm_num only [BoundaryTailProvider.cellNormal,BoundaryTailAlgebra.normalFlag,normal,w,hy,hz,
      hv2,FlagDegree.mk.injEq,true_and]
    omega
  have hraw : MovingFiberRetainedStage6811.rawFirstFlag (a+3+(b+2)+c) (a+3+(b+2)) (a+3) =
      raw a b c := by
    simp only [MovingFiberRetainedStage6811.rawFirstFlag,cellA,cellB,cellS,hz,hy,hb,hr2,
      RCN198.center,RCN198.direction,raw,w,unitYZFlag]
    change FlagDegree.mk (0+2*c+131071*c) (1+(2*(b+1)+1)+131071*(b+1+1))
      (0+(2*(a+1)+3)+131071*(a+1+2)) = _
    have e0 : 0+2*c+131071*c=131073*c := by ring
    have e1 : 1+(2*(b+1)+1)+131071*(b+1+1)=131073*b+262146 := by ring
    have e2 : 0+(2*(a+1)+3)+131071*(a+1+2)=131073*a+393218 := by ring
    rw [e0,e1,e2]
  have hw4 : 4*(w+1) = 524288 := rfl
  simp only [numberDir,graphDir,firstDir,hn,hraw,hw4]







end ProximityPrize.SubmissionLower.HFreeDirArith6814


