-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
-- name    : LeanPool_DeciSigma1_Holes_Fresh_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:44:05.468481+00:00
-- url     : https://prove2.me/theorems/064d57d9-fe12-4e0a-84c7-2632601ac156
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
def edgeText {t : ℕ} (e : Edge W t) : List α := (e.blocks.reverse.take e.endDepth).reverse.flatten
def edgePrefix {t : ℕ} (e : Edge W t) (p : ℕ) : List α :=
  edgeText e |>.take
      (firstBlocksLength e.blocks.reverse e.endDepth - firstBlocksLength e.blocks.reverse p)
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
def edgeMap {t : ℕ} (T : Table α S k) (e : Edge W t) (p : ℕ) : S → S :=
  fun q => runFrom T.step q ((edgePrefix e p).take
    ((edgePrefix e p).length - windowLength W t (edgePrefix e p) (edgePrefix e p).length))
def typeChoices (W : Fin k → List α) (r : ℕ) : Finset (Finset (List α)) :=
  insert ∅ ((active W r).image fun m => {marker W r m})
def lowerLevelTypeChoices (W : Fin k → List α) (t : ℕ) : Finset (Fin t → Finset (List α)) :=
  Fintype.piFinset fun r => typeChoices W (r.val + 1)
def jointLabel {t : ℕ} (T : Table α S k) (e : Edge W t) (p : ℕ) :
    (Fin t → Finset (List α)) × (S → S) :=
  (lowerLevelTypes W t (edgePrefix e p) (edgePrefix e p).length, edgeMap T e p)
def edgeLengthBound (k n : ℕ) : ℕ := (k + 1) ^ (k * n + 1) * n ^ n + 2 * deletionMargin k n + 1
def relativeCuts (A : Finset ℕ) (s e : ℕ) : Finset ℕ :=
  (A.filter fun q => s < q ∧ q ≤ e).image (fun q => q - s)
def occurrenceText (W : Fin k → List α) (o : Fin k × ℕ × ℕ) : List α :=
  ((W o.1).drop o.2.1).take (o.2.2 - o.2.1)
def occurrenceCuts (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : Finset ℕ :=
  relativeCuts (anchors W t o.1) o.2.1 o.2.2
def parseText (z : List α) (A : Finset ℕ) : List (List α) :=
  ((List.range A.card).map fun d =>
    (z.drop (depthCutAt A z.length (d + 1))).take (depthCutAt A z.length d - depthCutAt A z.length
        (d + 1))).reverse
def parseChoices (W : Fin k → List α) (t : ℕ) (z : List α) : Finset (List (List α)) :=
  (prefixOccurrenceCuts W
      z).powerset.image fun D => parseText z (insert z.length (contextAnchors W t z ∪ D))
def upperTexts (W : Fin k → List α) (t : ℕ) : Finset (List α) :=
  (upperOccurrences W t).image (occurrenceText W)
def parseFactor (k n : ℕ) : ℕ := 2 ^ (k * (n - 1))
def textCountBoundAtDepth (k n : ℕ) : ℕ → ℕ
  | 0 => k + 1
  | d + 1 => textCountBoundAtDepth k n d +
      (textCountBoundAtDepth k n d * parseFactor k n) *
        ((textCountBoundAtDepth k n d * parseFactor k n + 2) * edgeLengthBound k n)
def textCountBound (k n : ℕ) : ℕ := textCountBoundAtDepth k n (k * n)
def expansionBlockCountBound (k n : ℕ) :
    ℕ := (textCountBound k n * parseFactor k n + 2) * edgeLengthBound k n
def freshTupleBound (k n : ℕ) : ℕ := k * expansionBlockCountBound k n ^ (k * n + 1)
end DeciSigma1.Holes.Fresh


