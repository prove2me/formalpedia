-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
-- name    : LeanPool_BooleanIsoperimetry_Cube
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:13:53.97086+00:00
-- url     : https://prove2.me/theorems/0c51251c-f78a-412b-bae7-05d27f488688
-- title:
--   Cube
-- statement:
--   Definitions and structural lemmas for Cube, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry
abbrev Cube (n : ℕ) := Finset (Fin n)
noncomputable def hDist {n : ℕ} (x y : Cube n) : ℕ :=
  (symmDiff x y).card
noncomputable def neighborhood {n : ℕ} (r : ℕ) (A : Finset (Cube n)) : Finset (Cube n) :=
  Finset.univ.filter (fun v => ∃ u ∈ A, hDist u v ≤ r)
noncomputable def hammingBall {n : ℕ} (r : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun v => v.card ≤ r)
noncomputable def cubeToNat {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i ∈ x, 2 ^ (i : ℕ)
def simplicialLe {n : ℕ} (x y : Cube n) : Prop :=
  x.card < y.card ∨ (x.card = y.card ∧ cubeToNat y ≤ cubeToNat x)
def simplicialLt {n : ℕ} (x y : Cube n) : Prop :=
  simplicialLe x y ∧ ¬simplicialLe y x
open Classical in
/-- The zero-based position of a vertex in the simplicial order. -/
noncomputable def rank {n : ℕ} (x : Cube n) : ℕ :=
  (Finset.univ.filter (fun y => simplicialLt y x)).card
open Classical in
/-- The first `k` vertices of the `n`-cube in simplicial order. -/
noncomputable def simplicialInitSeg (n : ℕ) (k : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => rank x < k)
noncomputable def embed0 {n : ℕ} (x : Cube n) : Cube (n + 1) :=
  x.image Fin.castSucc
noncomputable def embed1 {n : ℕ} (x : Cube n) : Cube (n + 1) :=
  insert (Fin.last n) (x.image Fin.castSucc)
noncomputable def slice0 {n : ℕ} (A : Finset (Cube (n + 1))) : Finset (Cube n) :=
  Finset.univ.filter (fun x => embed0 x ∈ A)
noncomputable def slice1 {n : ℕ} (A : Finset (Cube (n + 1))) : Finset (Cube n) :=
  Finset.univ.filter (fun x => embed1 x ∈ A)
noncomputable def H (n k : ℕ) : ℕ :=
  (neighborhood 1 (simplicialInitSeg n k)).card
noncomputable def gShift {n : ℕ} (v : Cube n) : Cube n :=
  if h : v.Nonempty then v.erase (v.min' h) else v
def binomPrefix (n r : ℕ) : ℕ :=
  (Finset.range r).sum (fun i => Nat.choose n i)
def choosePred (n r : ℕ) : ℕ :=
  if r = 0 then 0 else Nat.choose n (r - 1)
end BooleanIsoperimetry


