-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
-- name    : Submission_ThreeSum_LightTernaryParallelDictionaries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:01.245186+00:00
-- url     : https://prove2.me/theorems/1f915b04-7337-4de8-aad1-f9cca94ff2b6
-- title:
--   Light Ternary Parallel Dictionaries
-- statement:
--   Definitions and structural lemmas for Light Ternary Parallel Dictionaries, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelDictionaries.lean

import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryParallelDictionaries
open Light RadixKeyLists
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
variable {lim : Limits}
def libraries (xs ys zs : List ℤ) : Program := ReportingHostRelocation.program
  (ReportingHostRelocation.program (LightFixedRadixDictionary.program xs)
    (LightFixedRadixDictionary.program ys)) (LightFixedRadixDictionary.program zs)
def body : Stmt :=
  .call 4 [v 0,v 1,v 6,v 7] 10 ;;
  .call 9 [v 2,v 3,v 6,v 8] 11 ;;
  .call 14 [v 4,v 5,v 6,v 9] 12 ;;
  .set 0 (v 12)
def program (xs ys zs : List ℤ) : Program := libraries xs ys zs++[body]
def time (xs ys zs : List ℤ) (J : ℕ) : ℕ :=
  LightFixedRadixDictionary.time xs J+LightFixedRadixDictionary.time ys J+
    LightFixedRadixDictionary.time zs J+100
def output (μ : ℕ → ℤ) (dst : ℕ) (xs : List ℤ) (p J : ℕ) : Prop :=
  μ (dst+LightRadixKeys.offset xs.length J)=((xs.length^J : ℕ) : ℤ) ∧
  Seg μ (dst+LightRadixKeys.offset xs.length J+1) (values (p : ℤ) xs J)
def recordOutput {R : Type*} (μ : ℕ → ℤ) (dst : ℕ) (records : List R)
    (raw : R → ℤ) (p J : ℕ) : Prop :=
  μ (dst+LightRadixKeys.offset records.length J)=((records.length^J : ℕ) : ℤ) ∧
  Seg μ (dst+LightRadixKeys.offset records.length J+1)
    ((tuples records J).map (Radix.positionalHash (p : ℤ) raw))
end ThreeSum.LightTernaryParallelDictionaries


