-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
-- name    : LeanPool_DeciSigma1_Holes_Fresh_Deletion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:42:11.920537+00:00
-- url     : https://prove2.me/theorems/01652511-9ac7-45b1-a286-bf0d17612644
-- title:
--   Deletion
-- statement:
--   Definitions and structural lemmas for Deletion, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
section OneSite
variable {W : Fin k → List α}
structure ValidDeletionSite (W : Fin k → List α) (t : ℕ) (x : List α) (c δ : ℕ) : Prop where
  le_len : c + δ ≤ x.length
  anchor : 1 ≤ t → ∃ m ∈ active W t, marker W t m <:+ x.take c
  types : ∀ r, 1 ≤ r → r ≤ t → ∀ m ∈ active W r,
    (marker W r m <:+ x.take c ↔ marker W r m <:+ x.take (c + δ))
  no_upper_marker : ∀ m ∈ active W (t + 1), ¬ marker W (t + 1) m <:+ x.take (c + δ)
end OneSite
section SeveralSites
variable {W : Fin k → List α}
def sitePositions (δ : ℕ) (cs : Finset ℕ) : Finset ℕ := cs.biUnion fun c => Finset.Ico c (c + δ)
def StrictlySeparated (δ : ℕ) (cs : Finset ℕ) : Prop := ∀ c ∈ cs, ∀ c' ∈ cs, c < c' → c + δ < c'
def Retained (δ : ℕ) (cs : Finset ℕ) (p : ℕ) : Prop := ∀ c ∈ cs, ¬ (c < p ∧ p < c + δ)
variable {δ : ℕ} {cs : Finset ℕ}
variable {S : Type}
end SeveralSites
section Label
variable {S : Type} [DecidableEq S]
def deletionMargin (k n : ℕ) : ℕ := (k * (n - 1) + 2) + 2 * k * n + 3
def markerTypes (W : Fin k → List α) (r : ℕ) (u : List α) (c : ℕ) : Finset (List α) :=
  ((active W r).filter (fun m => marker W r m <:+ u.take c)).image (marker W r)
def lowerLevelTypes (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) : Fin t → Finset (List α) :=
  fun r => markerTypes W (r.1 + 1) u c
def windowLength (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) : ℕ :=
  univ.sup fun r : Fin t => (lowerLevelTypes W t u c r).sup List.length
def label (T : Table α S k) (W : Fin k → List α) (t : ℕ) (l : Fin k) (c : ℕ) :
    (Fin t → Finset (List α)) × S :=
  (lowerLevelTypes W t (W l) c, T.runPrefix W l (c - windowLength W t (W l) c))
end Label
variable {S : Type} [Fintype S]
structure BlockDeletion (T : Table α S k) (W : Fin k → List α) (t : ℕ) where
  /-- Parse edge containing the blocks to delete. -/
  edge : Edge W t
  /-- First cut of the deleted block interval. -/
  minDepth : ℕ
  /-- Last cut of the deleted block interval. -/
  maxDepth : ℕ
  left_margin : edge.startDepth + deletionMargin k (Fintype.card S) ≤ minDepth
  minDepth_lt_maxDepth : minDepth < maxDepth
  right_margin : maxDepth + deletionMargin k (Fintype.card S) ≤ edge.endDepth
  labels_eq : ∀ o ∈ upperOccurrences W t, edge.TraversedBy o →
    label T W t o.1 (depthCut W t o maxDepth) = label T W t o.1 (depthCut W t o minDepth)
namespace BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
def deletionLength :
    ℕ := firstBlocksLength m.edge.blocks.reverse m.maxDepth -
        firstBlocksLength m.edge.blocks.reverse m.minDepth
def traversingOccurrences (l : Fin k) : Finset (Fin k × ℕ × ℕ) :=
  (upperOccurrences W t).filter (fun o => o.1 = l ∧ m.edge.TraversedBy o)
def sites (l : Fin k) :
    Finset ℕ := (m.traversingOccurrences l).image (fun o => depthCut W t o m.maxDepth)
def apply : Fin k → List α :=
  fun l => deletePositions (W l) (sitePositions m.deletionLength (m.sites l))
end BlockDeletion
end DeciSigma1.Holes.Fresh


