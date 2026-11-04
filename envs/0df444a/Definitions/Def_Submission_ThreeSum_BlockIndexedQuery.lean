-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
-- name    : Submission_ThreeSum_BlockIndexedQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:31:25.791812+00:00
-- url     : https://prove2.me/theorems/516198ba-916e-4d1f-b058-ca9f2c58e1ca
-- title:
--   Block Indexed Query
-- statement:
--   Definitions and structural lemmas for Block Indexed Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndexedQuery.lean

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
namespace ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
def suffixStage (J L k : ℕ) : ℕ := (J-k)*L
def leftPrefix {J L : ℕ} (k : ℕ) (u : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (prefixLeft (prefixIndices J k) u)
def rightPrefix {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (prefixRight (prefixIndices J k) Q u)
def querySet {J L : ℕ} (k : ℕ) (Q : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (remaining (prefixIndices J k) Q)
section Histograms
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
def leftSource {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h))
    (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ))
def rightSource {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (q : GlobalOutput h J) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h))
    (fun S => (rightWeights (outputOccurrences q) P d C c S : ℤ))
def queryValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (k : ℕ)
    (u : Fin J → Finset (Fin (512*h))) : ℤ :=
  Subset.mobius (fun S =>
    SubsetStages.stageValue (leftSource P B b q) (suffixStage J (512*h) k) (leftPrefix k u ∪ S) *
    SubsetStages.stageValue (rightSource P d C c q) (suffixStage J (512*h) k)
      (rightPrefix k (outputRows q) u ∪ S)) (querySet k (outputRows q))
end Histograms
end ThreeSum.BlockIndexedQuery


