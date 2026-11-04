-- Prove2me | Definitions.Def_Submission_ThreeSum_RawReporting
-- name    : Submission_ThreeSum_RawReporting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:16:06.247472+00:00
-- url     : https://prove2.me/theorems/cb56b6c7-a14c-4e9c-b31a-a7256996541d
-- title:
--   Raw Reporting
-- statement:
--   Definitions and structural lemmas for Raw Reporting, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
set_option autoImplicit false
namespace ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
def colexEmbedding (L : ℕ) : Finset (Fin L) ↪ Colex (Finset (Fin L)) :=
  ⟨toColex, fun _ _ h => h⟩
def childList {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) : List (Finset (Fin L)) :=
  (((Q.powersetCard h).map (colexEmbedding L)).sort (· ≤ ·)).map ofColex
def children {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Fin (512 * h))) :=
  if hk : k < J then childList (q ⟨k, hk⟩).2.val h else []
def partitionWord {h J : ℕ} (t : ChoiceTuple h J) : List (Finset (Fin (512 * h))) :=
  List.ofFn fun i => (edge (t i)).val.1
theorem partitionWord_length {h J : ℕ} (t : ChoiceTuple h J) : (partitionWord t).length = J :=
  List.length_ofFn
instance outputBlockDecidableEq (h : ℕ) : DecidableEq (OutputBlock h) := inferInstance
instance globalOutputDecidableEq (h J : ℕ) : DecidableEq (GlobalOutput h J) :=
  Fintype.decidablePiFintype
abbrev Wanted (h J : ℕ) (α : Type*) := α × (Fin 3 × GlobalOutput h J)
instance wantedDecidableEq (h J : ℕ) (α : Type*) [DecidableEq α] :
    DecidableEq (Wanted h J α) := inferInstance
def wantedOf {h J : ℕ} {α β γ : Type*} (r : RawItem h J α β γ) : Wanted h J α :=
  (r.1.1, (r.2.2, tupleOutput r.2.1))
def word {h J : ℕ} {α β γ : Type*} (r : RawItem h J α β γ) := partitionWord r.2.1
section FixedBand
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def domain {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :=
  I.filter fun r => wantedOf r = w
def prefixQuery {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  Reporting.mass (domain I w) word (fun _ => 1) k pre
def frontier {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) : List (List (Finset (Fin (512 * h)))) :=
  Reporting.frontier (children w.2.2) (prefixQuery I w) k
end FixedBand
end ThreeSum.RawReporting


