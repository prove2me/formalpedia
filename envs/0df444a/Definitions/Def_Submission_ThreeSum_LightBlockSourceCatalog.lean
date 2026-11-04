-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
-- name    : Submission_ThreeSum_LightBlockSourceCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:43:08.938808+00:00
-- url     : https://prove2.me/theorems/423030da-7a4f-49ee-abf4-9b0568dd30aa
-- title:
--   Light Block Source Catalog
-- statement:
--   Definitions and structural lemmas for Light Block Source Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceCatalog.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBlockSourceCatalog
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def count (h J : ℕ) : ℕ := scheduleSize h^J
def body (pRows pBatch : ℕ) : Stmt :=
  .call pRows [v 16,v 0,v 23,v 7,v 22] 24 ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
    v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22] 24
def time (h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (count h J) J+
    LightBlockSourceBatch.time (count h J) h J cut+400
def space (base h J cut : ℕ) : ℕ :=
  max (LightBlockSourceRetainedHost.space (work base (count h J) (J*(512*h)) cut) h J)
    (LightOutputDecodeDigits.space (work base (count h J) (J*(512*h)) cut) (count h J))
def word (NL NR h J : ℕ) : ℕ :=
  max (LightBlockSourceRetainedHost.word NL NR h J)
    (LightOutputDecodeDigits.word (count h J) (scheduleSize h) J)
structure Procs (P : Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBatch : ℕ
  rows : P[pRows]? = some (LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]? = some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]? = some LightOutputDecodeDivide.body
  batch : LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]? = some (body pRows pBatch)
def Stored {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J base cut : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) : Prop :=
  ∀ i < count h J, LightBlockSourceBatch.BankAt μ base (count h J) cut i P shift B b A a
    (representative h J i)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceCatalog


