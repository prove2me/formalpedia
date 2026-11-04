-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockForced
-- name    : Submission_ThreeSum_BlockForced
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:25:28.553907+00:00
-- url     : https://prove2.me/theorems/29ba2a1b-40df-463a-a20f-e73cfe2ada1c
-- title:
--   Block Forced
-- statement:
--   Definitions and structural lemmas for Block Forced, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean

import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
namespace ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
section FiniteRows
variable {J L : ℕ}
def prefixLeft (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) := join I u
def prefixRight (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L)) :=
  join I fun i => Q i \ u i
def remaining (I : Finset (Fin J)) (Q : Fin J → Finset (Fin L)) := join Iᶜ Q
def suffixDomain (I : Finset (Fin J)) : Finset (Coord J L) := join Iᶜ fun _ => univ
end FiniteRows
def outputRows {h J : ℕ} (q : GlobalOutput h J) : Fin J → Finset (Fin (512 * h)) :=
  fun i => (q i).2.val
def completedTuples {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : Finset (ChoiceTuple h J) :=
  univ.filter fun t => tupleOutput t = q ∧ ∀ i ∈ I, (edge (t i)).val.1 = u i
def residual {h J : ℕ} (I : Finset (Fin J)) (t : ChoiceTuple h J) :=
  join Iᶜ fun i => (edge (t i)).val.1
def admissibleResiduals {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : Finset (Finset (Coord J (512 * h))) :=
  (remaining I (outputRows q)).powerset.filter fun x =>
    LeftAllowed (outputOccurrences q) (prefixLeft I u ∪ x) ∧
    RightAllowed (outputOccurrences q)
      (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x))
section WeightedCounts
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
def transformPrefixValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : ℤ :=
  Subset.mobius (fun z =>
    Subset.partialZeta (suffixDomain I)
      (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ)) (prefixLeft I u ∪ z) *
    Subset.partialZeta (suffixDomain I)
      (fun V => (rightWeights (outputOccurrences q) P d C c V : ℤ))
      (prefixRight I (outputRows q) u ∪ z))
    (remaining I (outputRows q))
end WeightedCounts
end ThreeSum.BlockForced


