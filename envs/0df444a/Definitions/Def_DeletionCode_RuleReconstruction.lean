-- Prove2me | Definitions.Def_DeletionCode_RuleReconstruction
-- name    : DeletionCode_RuleReconstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:16:55.412969+00:00
-- url     : https://prove2.me/theorems/9cfb1c23-a450-4b71-8774-c1c203e89225
-- title:
--   Rule Reconstruction
-- statement:
--   Definitions and structural lemmas for Rule Reconstruction, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
set_option autoImplicit true
namespace DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
def negativeLetters {ν : ℕ} (data : RecoveredData ν) (b : Fin ν) : Letters :=
  fun i => (data.words b).getD i false
def recoveredFamily {ν : ℕ} (k : ℕ) (rank : Fin ν → ℕ)
    (data : RecoveredData ν) : Family (Fin ν) where
  rank := rank
  path b side := if side then rebuildPositive k (data.header b) (negativeLetters data b)
    else negativeLetters data b
  extra b side := PathMemory.pathLength k (data.header b) side - windowLength k
def groupBubbles {ν R : ℕ} (group : Fin ν → Fin R) (r : Fin R) : Finset (Fin ν) :=
  Finset.univ.filter (fun b => group b = r)
noncomputable def rulesOfFamily {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) : Finset (Gram (windowLength k) → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum E.family (windowLength k) (groupBubbles group r))
noncomputable def rulesOfData {ν R : ℕ} (k : ℕ) (group : Fin ν → Fin R)
    (data : RecoveredData ν) : Finset (Gram (windowLength k) → ℤ) := by
  classical
  exact Finset.univ.image (fun r => ruleSpectrum
    (recoveredFamily k (fun b => (group b).val) data) (windowLength k) (groupBubbles group r))
end DeletionCode.RuleReconstruction


