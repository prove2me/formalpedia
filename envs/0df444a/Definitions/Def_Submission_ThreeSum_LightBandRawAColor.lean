-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawAColor
-- name    : Submission_ThreeSum_LightBandRawAColor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:45:42.332202+00:00
-- url     : https://prove2.me/theorems/62f7b8bd-e8ff-438c-a134-99e6f3bd604b
-- title:
--   Light Band Raw AColor
-- statement:
--   Definitions and structural lemmas for Light Band Raw AColor, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAColor.lean

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Theorems.Thm_Light_Ends_call
set_option autoImplicit false
namespace ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
def body (pColor pCatalog : ℕ) : Stmt :=
  _root_.Light.Stmt.seq
    (.call pColor
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19,
        v 20]
      23)
    (.call pCatalog [v 20, v 21, v 14, v 15, v 17, v 19, v 13, v 22] 0)
def catalogTime (n g : ℕ) : ℕ :=
  3000 * (ColorBandBounds.count n g + 3 * size n g + 1) * (g + 1)
def time (W n g : ℕ) : ℕ :=
  LightColorBands.time W n g + catalogTime n g + 300
def space (work vals W n g : ℕ) : ℕ :=
  max (LightColorBands.space work W n g) (LightBandRawA.space vals (ColorBandBounds.count n g) g)
def word (W n g U : ℕ) : ℕ :=
  LightColorBands.word W n g U + LightBandRawACatalog.word n (size n g) (size n g) (size n g) g
def depth (W n g : ℕ) : ℕ :=
  LightColorBands.depth W n g + 5
def Output (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g) (originalA originalB originalC : List ℤ)
    (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·)) (C : List ℤ) (hsC :
    C.Pairwise (· < ·)),
    let rs := sortedRecords A B C g hg hsA hsB hsC
    r = ((items A.length g rs).length : ℤ) ∧
      LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
        LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
          LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
            LightBandEnumeration.Tables μ tables
                (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
                (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
                (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)) ∧
              Seg μ rec (cells rs) ∧
                Stored μ vals (LightBandRawA.ownerBase vals rs.length g) (LightBandRawA.positionBase vals rs.length g)
                  (fun i => A.getD i 0) (items A.length g rs)
structure Procs (P : Program) (pMain : ℕ) where
  pColor : ℕ
  pCatalog : ℕ
  color : LightColorBands.Procs P pColor
  catalog : LightBandRawACatalog.Procs P pCatalog
  main : P[pMain]? = some (body pColor pCatalog)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  LightColorBands.program ++
    [LightBandRawACatalog.body 28 38, LightBandCandidates.body 29 32 35, LightBandCandidatesTable.body 30,
      LightBandCandidatesRow.body 31, LightBandCandidatesCell.body .bc, LightBandCandidatesTable.body 33,
      LightBandCandidatesRow.body 34, LightBandCandidatesCell.body .ab, LightBandCandidatesTable.body 36,
      LightBandCandidatesRow.body 37, LightBandCandidatesCell.body .ac, LightBandRawA.body 39,
      LightBandRawAStep.body 40, LightBandRawARow.body 41 42, copyBody, fillBody, body 20 27]
def programProcs : Procs program 43 where
  pColor := 20
  pCatalog := 27
  color :=
    { pClasses := 21
      pBands := 0
      classes := ⟨22, 23, 24, 25, 26, rfl, rfl, rfl, rfl, rfl, rfl⟩
      bands :=
        { pPrepare := 1
          pEnumerate := 12
          prepare := ⟨2, 8, 9, 10, 11, ⟨3, 4, 5, 6, 7, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
          enumerate := ⟨13, ⟨14, 15, 16, 17, 18, 19, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
          main := rfl }
      main := rfl }
  catalog :=
    { pCandidates := 28
      pRaw := 38
      candidates := ⟨29, 32, 35, 30, 33, 36, 31, 34, 37, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      raw := ⟨39, 40, 41, 42, rfl, rfl, rfl, rfl, rfl⟩
      main := rfl }
  main := rfl
end ThreeSum.LightBandRawAColor


