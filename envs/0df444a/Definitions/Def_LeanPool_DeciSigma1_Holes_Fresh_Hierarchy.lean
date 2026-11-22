-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
-- name    : LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:36.929276+00:00
-- url     : https://prove2.me/theorems/602da65f-74b6-46f1-ae00-8a48f9474b92
-- title:
--   Hierarchy
-- statement:
--   Definitions and structural lemmas for Hierarchy, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
section Occurrences
variable {x u v : List α}
end Occurrences
structure Level (α : Type) (k : ℕ) where
  /-- Coordinates participating in this level. -/
  active : Finset (Fin k)
  /-- Distinguishing word assigned to each participating coordinate. -/
  marker : Fin k → List α
namespace Level
variable [DecidableEq α] (L : Level α k)
def markerEndCuts (u : List α) : Finset ℕ :=
  (range (u.length + 1)).filter (fun e => ∃ m ∈ L.active, L.marker m <:+ u.take e)
def lastInteriorCut (x : List α) : ℕ := ((L.markerEndCuts x).filter (· < x.length)).sup id
def blockLengthAt (x : List α) (e : ℕ) : ℕ :=
  (L.active.filter (fun m => L.marker m <:+ x.take e)).sup (fun m => (L.marker m).length)
def next (W : Fin k → List α) : Level α k where
  active := L.active.filter (fun l => ∃ e ∈ L.markerEndCuts (W l), e < (W l).length)
  marker l := (W l).drop (L.lastInteriorCut (W l) - L.blockLengthAt (W l) (L.lastInteriorCut (W l)))
variable {L}
def FactorAntichain (L : Level α k) : Prop :=
  (∀ m ∈ L.active, L.marker m ≠ []) ∧
    ∀ m ∈ L.active, ∀ m' ∈ L.active, L.marker m <:+: L.marker m' → L.marker m = L.marker m'
def MarkersAreSuffixes (L : Level α k) (W : Fin k → List α) :
    Prop := ∀ m ∈ L.active, L.marker m <:+ W m
end Level
variable [DecidableEq α]
def level (W : Fin k → List α) : ℕ → Level α k
  | 0 => ⟨univ.filter (fun l => W l ≠ []), fun _ => []⟩
  | 1 => ⟨univ.filter (fun l => W l ≠ []), fun l => (W l).drop ((W l).length - 1)⟩
  | t + 2 => (level W (t + 1)).next W
def active (W : Fin k → List α) (t : ℕ) : Finset (Fin k) := (level W t).active
def marker (W : Fin k → List α) (t : ℕ) : Fin k → List α := (level W t).marker
def contextAnchors (W : Fin k → List α) : ℕ → List α → Finset ℕ
  | 0, u => Icc 1 u.length
  | t + 1, u => (level W (t + 1)).markerEndCuts u
def anchors (W : Fin k → List α) (t : ℕ) (l : Fin k) : Finset ℕ :=
  insert (W l).length (contextAnchors W t (W l))
def topLevel (W : Fin k → List α) : ℕ :=
  Nat.find (⟨totalLength W, Or.inr le_rfl⟩ : ∃ t, active W (t + 1) = ∅ ∨ totalLength W ≤ t)
section Basic
variable (W : Fin k → List α)
end Basic
section Antichain
variable {W : Fin k → List α}
end Antichain
section Locality
variable {W : Fin k → List α}
end Locality
section Top
variable {W : Fin k → List α}
end Top
section Fresh
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
def suffixOccurrenceCuts (W : Fin k → List α) (j : Fin k) (z : List α) : Finset ℕ :=
  (range (W j).length).filter (fun b => (W j).drop b <+: z)
def prefixOccurrenceCuts (W : Fin k → List α) (z : List α) : Finset ℕ :=
  (Icc 1 z.length).filter (fun p => ∃ j, z.take p <:+ W j)
end Fresh
end DeciSigma1.Holes.Fresh


