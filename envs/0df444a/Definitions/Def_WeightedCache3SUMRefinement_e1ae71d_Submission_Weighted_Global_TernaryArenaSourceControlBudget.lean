-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:04:59.7275+00:00
-- url     : https://prove2.me/theorems/68c8df50-2e3d-4bb6-825c-a739d636df2c
-- title:
--   TernaryArenaSourceControlBudget
-- statement:
--   Definitions and structural lemmas for TernaryArenaSourceControlBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControls
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
def baseWord (m p F r : ℕ) : ℕ :=
  LightRadixKeys.word p p r+LightRadixKeys.word (4^fixedLength m) (4^fixedLength m) r+
    LightRadixKeys.word F F r+LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0+
    (4^(N m r)+2^(2*N m r+1)+16)+(F^r*4^(N m r)+1)+2^(r*fixedAlpha m 2)
def weightCoefficient (m R r n : ℕ) : ℕ :=
  2^(r*fixedAlpha m 2)*(n*R^r)+(n*R^r+1)
def upperWord (m p F R r n w : ℕ) : ℕ :=
  baseWord m p F r+weightCoefficient m R r n*w
def Poly (f : ℕ→ℕ) : Prop :=∃ a : ℝ, PowerBound f a
def budget (m p F R M W E n U : ℕ) : Need :=
  ⟨(baseWord m p F (Nat.clog M (n^2))+
      weightCoefficient m R (Nat.clog M (n^2)) n*(W+1))*(U+1)^E,
    0,n+2*N m (Nat.clog M (n^2))+Nat.clog M (n^2)+8⟩
end ThreeSum.WeightedGlobalArenaSourceControlBudget
end
end WeightedCache3SUMRefinement_e1ae71d


