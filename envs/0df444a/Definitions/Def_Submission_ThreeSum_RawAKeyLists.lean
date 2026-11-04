-- Prove2me | Definitions.Def_Submission_ThreeSum_RawAKeyLists
-- name    : Submission_ThreeSum_RawAKeyLists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:48:40.281204+00:00
-- url     : https://prove2.me/theorems/99d24a20-b6ca-4ee0-a94d-c436783dfc8e
-- title:
--   Raw AKey Lists
-- statement:
--   Definitions and structural lemmas for Raw AKey Lists, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
namespace ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
abbrev Record (xs : List ℤ) := Fin 3 × Fin xs.length
def records (xs : List ℤ) : List (Record xs) :=
  (List.finRange 3).product (List.finRange xs.length)
def key (P : ℤ) (xs : List ℤ) (r : Record xs) : ℤ :=
  xs.getD r.2.val 0 % P+lift r.1*P
def keys (P : ℤ) (xs : List ℤ) : List ℤ := (records xs).map (key P xs)
theorem records_nodup (xs : List ℤ) : (records xs).Nodup :=
  (List.nodup_finRange 3).product (List.nodup_finRange xs.length)
theorem mem_records (xs : List ℤ) (r : Record xs) : r ∈ records xs := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩
noncomputable def recordEquiv (xs : List ℤ) : Fin (records xs).length ≃ Record xs :=
  Equiv.ofBijective (records xs).get
    ⟨(records_nodup xs).injective_get,fun r => List.mem_iff_get.mp (mem_records xs r)⟩
def guardedCount (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) : ℕ :=
  ∑ i : Fin xs.length, ∑ j : Fin 3, ∑ q : GlobalOutput h J,
    if (M : ℤ) ∣ xs.getD i.val 0%P+lift j*P+d-globalKey q then 1 else 0
def selected (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) : ℕ :=
  GlobalKeyOffset.selected M (keys P xs) h J
def wanted (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    Finset (RawReporting.Wanted h J (Fin xs.length)) :=
  Finset.univ.filter fun w =>
    (M : ℤ) ∣ xs.getD w.1.val 0%P+lift w.2.1*P+d-globalKey w.2.2
end ThreeSum.RawAKeyLists


