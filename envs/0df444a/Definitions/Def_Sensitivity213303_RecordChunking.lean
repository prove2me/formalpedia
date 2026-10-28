-- Prove2me | Definitions.Def_Sensitivity213303_RecordChunking
-- name    : Sensitivity213303_RecordChunking
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:59:13.536697+00:00
-- url     : https://prove2.me/theorems/609bdb84-a050-47c9-9264-457c891aac54
-- title:
--   Bounded chunks of the exact finite case checker
-- statement:
--   The chunk checker selects active candidate kinds and tests bounded portions of the executable orientation enumeration against a record lookup tree. checkCasesFrom advances from a specified offset, and checkCasesChunk limits one certificate to a finite block. Splitting the exhaustive check into such blocks keeps each kernel verification bounded while preserving the same complete case set.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module RecordChunking; source SHA256 2e3bc9e8cc2dc604b6e711bf235c3b6294700cf8612dec7e45e019a90f1547c3.

/- Composition of bounded exhaustive-enumeration checks. -/
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecordSetLookup
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop



set_option autoImplicit false

namespace ThreeBoundRecordLookup









def activeTypes (n : ℕ) : List (List ThreeBoundQ2.Kind) :=
  (ThreeBoundQ2.typeLists 0 n).filter fun ts => decide (ThreeBoundQ2.allowedTypes ts)



def checkCasesChunk (tree : Tree) (ts : List ThreeBoundQ2.Kind) (start count : ℕ) : Bool :=
  (((ThreeBoundQ2.casesFor ts).drop start).take count).all fun c => tree.contains (recordFast c)

def checkCasesFrom (tree : Tree) (ts : List ThreeBoundQ2.Kind) (start : ℕ) : Bool :=
  ((ThreeBoundQ2.casesFor ts).drop start).all fun c => tree.contains (recordFast c)









end ThreeBoundRecordLookup


