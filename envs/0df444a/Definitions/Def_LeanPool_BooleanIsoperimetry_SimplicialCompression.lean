-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
-- name    : LeanPool_BooleanIsoperimetry_SimplicialCompression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:18.576073+00:00
-- url     : https://prove2.me/theorems/1e18b8d9-0231-4562-b929-b1fa2508533c
-- title:
--   Simplicial Compression
-- statement:
--   Definitions and structural lemmas for Simplicial Compression, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
open Finset
namespace BooleanIsoperimetry
def IsCoordinateUp {N : ℕ} (i : Fin N) (A A' : Finset (Cube N)) : Prop :=
  A'.card = A.card ∧
  ∀ x, x ∈ A' ↔ (x ∈ A ∧ (i ∈ x ∨ insert i x ∈ A)) ∨ (i ∈ x ∧ x ∉ A ∧ x.erase i ∈ A)
def IsCoordinateDown {N : ℕ} (i : Fin N) (B B' : Finset (Cube N)) : Prop :=
  B'.card = B.card ∧
  ∀ x, x ∈ B' ↔ (x ∈ B ∧ (i ∉ x ∨ x.erase i ∈ B)) ∨ (i ∉ x ∧ x ∉ B ∧ insert i x ∈ B)
noncomputable def coordinateUp {N : ℕ} (i : Fin N) (A : Finset (Cube N)) : Finset (Cube N) :=
  let A_kept := A.filter (fun x => i ∈ x ∨ insert i x ∈ A)
  let A_moved := (A.filter (fun x => i ∉ x ∧ insert i x ∉ A)).image (fun x => insert i x)
  A_kept ∪ A_moved
noncomputable def coordinateDown {N : ℕ} (i : Fin N) (A : Finset (Cube N)) : Finset (Cube N) :=
  let A_kept := A.filter (fun x => i ∉ x ∨ erase x i ∈ A)
  let A_moved := (A.filter (fun x => i ∈ x ∧ erase x i ∉ A)).image (fun x => erase x i)
  A_kept ∪ A_moved
noncomputable def compressionPotential {N : ℕ} (A : Finset (Cube N)) : ℕ :=
  ∑ x ∈ A, rank x
noncomputable def pairCompressionPotential {N : ℕ} (A B : Finset (Cube N)) : ℕ :=
  compressionPotential A + compressionPotential B
def IsCoordinateUpFixed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ i : Fin N, IsCoordinateUp i A A
def IsCoordinateDownFixed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ i : Fin N, IsCoordinateDown i A A
noncomputable def downMap {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) : Cube N :=
  if i ∈ x ∧ x.erase i ∉ A then x.erase i else x
def IsColexShift {N : ℕ} (A A' : Finset (Cube N)) : Prop :=
  A'.card = A.card ∧
  ∃ (x y : Cube N), x ∈ A ∧ y ∉ A ∧ x.card = y.card ∧ simplicialLt y x ∧
    A' = insert y (A.erase x)
def IsColexShiftFixed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ A', ¬IsColexShift A A'
def IsLowerLevelSaturated {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ ⦃x y : Cube N⦄, x.card < y.card → y ∈ A → x ∈ A
noncomputable def initialSlicePair (N a b : ℕ) : Finset (Cube (N + 1)) :=
  (simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1
end BooleanIsoperimetry


