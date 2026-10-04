-- Prove2me | Definitions.Def_Conway99_Boundary_Walk_20261003
-- name    : Conway99_Boundary_Walk_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-03T23:54:16.289586+00:00
-- url     : https://prove2.me/theorems/8fa903eb-fcdc-4eef-bde9-1a12e6cd4aa2
-- title:
--   Graph-owned boundary walk blocks and necessary conditions
-- statement:
--   For one hypothetical SRG(99,14,1,2), choose a root and any patch of its far vertices. Take the patch adjacency, patch/outside incidence, outside adjacency, and near-incidence blocks from that same graph. The far P3 equation gives exact formulas for T = X Y Xᵀ and U = X Y² Xᵀ in terms of D = X Xᵀ, R = X N_O, and e = X 1. T is symmetric, entrywise nonnegative, and has even diagonal; U is entrywise nonnegative; the joint block [D T; T U] is a real positive semidefinite Gram matrix. These are necessary conditions. The cited C3 fixture survives them.
-- source:
--   adversarial-review-r230/scratchpad/theorem_hunt/cycle_core_residual_theorem/breakthrough_global_mu2_handoff.md, SHA-256 fe7716e070bc9cd24fcca118ba9bfce7fae52e5ce53954da7f7e347eddb49323, lines 73-143; rooted far P3 proved from Conway99/Conway99/Verified/Rooted.lean at base 425f6e4.

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.BoundaryWalkGram

open Matrix

variable {P O L : Type*} [Fintype P] [Fintype O] [Fintype L]
  [DecidableEq P] [DecidableEq O] [DecidableEq L]

def ones (I J : Type*) : Matrix I J ℤ := Matrix.of fun _ _ => 1
def allOnes (m n : Type*) (α : Type*) [One α] : Matrix m n α := Matrix.of fun _ _ => 1
def D (X : Matrix P O ℤ) : Matrix P P ℤ := X * Xᵀ
def R (X : Matrix P O ℤ) (NO : Matrix O L ℤ) : Matrix P L ℤ := X * NO
def e (X : Matrix P O ℤ) : Matrix P Unit ℤ := X * ones O Unit
def T (X : Matrix P O ℤ) (Y : Matrix O O ℤ) : Matrix P P ℤ := X * Y * Xᵀ
def U (X : Matrix P O ℤ) (Y : Matrix O O ℤ) : Matrix P P ℤ := X * (Y * Y) * Xᵀ
def walkRows (X : Matrix P O ℤ) (Y : Matrix O O ℤ) :
    Matrix (P ⊕ P) O ℤ := Matrix.fromRows X (X * Y)
def jointGram (X : Matrix P O ℤ) (Y : Matrix O O ℤ) :
    Matrix (P ⊕ P) (P ⊕ P) ℤ :=
  Matrix.fromBlocks (D X) (T X Y) (T X Y) (U X Y)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

def actualLocF : Finset V := G.neighborFinset r
def actualFarF : Finset V := Finset.univ \ insert r (actualLocF G r)
abbrev actualLocT := {x : V // x ∈ actualLocF G r}
abbrev actualFarT := {x : V // x ∈ actualFarF G r}
def actualAFar : Matrix (actualFarT G r) (actualFarT G r) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun x => x.1)
def actualNReg : Matrix (actualFarT G r) (actualLocT G r) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun x => x.1)
def actualMMate : Matrix (actualLocT G r) (actualLocT G r) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun x => x.1)

variable {F : Type*} [Fintype F] [DecidableEq F]

abbrev Patch (S : Finset F) := {x : F // x ∈ S}
abbrev Outside (S : Finset F) := {x : F // x ∈ Finset.univ \ S}
def patchAdj (A : Matrix F F ℤ) (S : Finset F) : Matrix (Patch S) (Patch S) ℤ :=
  A.submatrix Subtype.val Subtype.val
def boundaryIncidence (A : Matrix F F ℤ) (S : Finset F) :
    Matrix (Patch S) (Outside S) ℤ :=
  A.submatrix Subtype.val Subtype.val
def outsideAdj (A : Matrix F F ℤ) (S : Finset F) :
    Matrix (Outside S) (Outside S) ℤ :=
  A.submatrix Subtype.val Subtype.val
def patchNear {L : Type*} (N : Matrix F L ℤ) (S : Finset F) :
    Matrix (Patch S) L ℤ := N.submatrix Subtype.val id
def outsideNear {L : Type*} (N : Matrix F L ℤ) (S : Finset F) :
    Matrix (Outside S) L ℤ := N.submatrix Subtype.val id

def actualConditions {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (S : Finset (actualFarT G r)) : Prop :=
  let A := actualAFar G r
  let N := actualNReg G r
  let AP := patchAdj A S
  let X := boundaryIncidence A S
  let Y := outsideAdj A S
  let NP := patchNear N S
  let NO := outsideNear N S
  T X Y = 2 • (ones (Patch S) Unit * (e X)ᵀ) -
      NP * (R X NO)ᵀ - AP * D X - D X ∧
  U X Y = 12 • D X - T X Y + 2 • (e X * (e X)ᵀ) -
      R X NO * (R X NO)ᵀ - D X * D X ∧
  (T X Y)ᵀ = T X Y ∧
  (∀ i j, 0 ≤ T X Y i j) ∧
  (∀ i, Even (T X Y i i)) ∧
  (∀ i j, 0 ≤ U X Y i j) ∧
  ((jointGram X Y).map (Int.castRingHom ℝ)).PosSemidef

end Conway99Formal.BoundaryWalkGram


