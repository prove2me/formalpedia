-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
-- name    : Submission_Weighted_Global_TernaryArenaSourceControlBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:07:57.242193+00:00
-- url     : https://prove2.me/theorems/7755ba2d-87ee-4cc1-9a88-259067b42f70
-- title:
--   Ternary Arena Source Control Budget
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Control Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
set_option autoImplicit false
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


