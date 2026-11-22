-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
-- name    : LeanPool_DeciSigma1_Holes_Fresh_Parsing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:53.349971+00:00
-- url     : https://prove2.me/theorems/13d9df8a-c5d2-4398-9de3-c41d4833ee0b
-- title:
--   Parsing
-- statement:
--   Definitions and structural lemmas for Parsing, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open Finset
section Lcp
variable {β : Type} [DecidableEq β]
def commonPrefixLength : List β → List β → ℕ
  | a :: A, b :: B => if a = b then commonPrefixLength A B + 1 else 0
  | _, _ => 0
def commonSuffixLength (Z Y : List β) : ℕ := commonPrefixLength Z.reverse Y.reverse
end Lcp
section Cuts
def previousAnchor (A : Finset ℕ) (p : ℕ) : ℕ := (A.filter (· < p)).sup id
def depthCutAt (A : Finset ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | d + 1 => previousAnchor A (depthCutAt A e d)
def anchorCount (A : Finset ℕ) (s e : ℕ) : ℕ := (A.filter (fun p => s < p ∧ p ≤ e)).card
variable {A : Finset ℕ}
end Cuts
section Upper
variable {α : Type} [DecidableEq α] {k : ℕ}
def upperOccurrenceStart (W : Fin k → List α) (t : ℕ) (l : Fin k) (e : ℕ) : ℕ :=
  previousAnchor (anchors W (t + 1) l) e
def upperOccurrences (W : Fin k → List α) (t : ℕ) : Finset (Fin k × ℕ × ℕ) :=
  (univ.filter fun l => W l ≠ []).biUnion fun l =>
    (anchors W (t + 1) l).image fun e => (l, upperOccurrenceStart W t l e, e)
def lowerBlockCount (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : ℕ :=
  anchorCount (anchors W t o.1) o.2.1 o.2.2
def depthCut (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) (d : ℕ) : ℕ :=
  depthCutAt (anchors W t o.1) o.2.2 d
def reversedBlocks (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : List (List α) :=
  (List.range (lowerBlockCount W t o)).map fun d =>
    ((W o.1).drop (depthCut W t o (d + 1))).take (depthCut W t o d - depthCut W t o (d + 1))
def upperParse (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : List (List α) :=
  (reversedBlocks W t o).reverse
def upperParses (W : Fin k → List α) (t : ℕ) : Finset (List (List α)) :=
  (upperOccurrences W t).image (upperParse W t)
def firstBlocksLength {β : Type} (Z : List (List β)) (d : ℕ) : ℕ := ((Z.take d).map List.length).sum
def trieNodes (W : Fin k → List α) (t : ℕ) (Z : List (List α)) : Finset ℕ :=
  insert 0 (insert Z.length ((upperParses W t).image (commonSuffixLength Z)))
structure Edge (W : Fin k → List α) (t : ℕ) where
  /-- Common blocks parsed along this edge. -/
  blocks : List (List α)
  blocks_mem : blocks ∈ upperParses W t
  /-- Initial trie cut of the parsed block interval. -/
  startDepth : ℕ
  /-- Final trie cut of the parsed block interval. -/
  endDepth : ℕ
  endDepth_mem : endDepth ∈ trieNodes W t blocks
  startDepth_lt_endDepth : startDepth < endDepth
  no_interior_node : ∀ c ∈ trieNodes W t blocks, ¬ (startDepth < c ∧ c < endDepth)
def Edge.TraversedBy {W : Fin k → List α} {t : ℕ} (e : Edge W t) (o : Fin k × ℕ × ℕ) : Prop :=
  e.endDepth ≤ commonSuffixLength (upperParse W t o) e.blocks
instance {W : Fin k → List α} {t : ℕ} (e : Edge W t) (o : Fin k × ℕ × ℕ) :
    Decidable (e.TraversedBy o) := inferInstanceAs (Decidable (_ ≤ _))
namespace Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)
end Edge
end Upper
section Locality
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
def relativeAnchors (W : Fin k → List α) (t : ℕ) (u z : List α) : Finset ℕ :=
  (Icc 1 z.length).filter (fun p => u.length + p ∈ contextAnchors W t (u ++ z))
def crossBoundaryMarkerEnds (W : Fin k → List α) (t : ℕ) (u z : List α) : Finset ℕ :=
  (Icc 1 z.length).filter (fun p => ∃ m ∈ active W t,
    marker W t m <:+ (u ++ z).take (u.length + p) ∧ p < (marker W t m).length)
end Locality
end DeciSigma1.Holes.Fresh


