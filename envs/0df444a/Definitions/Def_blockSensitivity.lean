-- Prove2me | Definitions.Def_blockSensitivity
-- name    : blockSensitivity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-04-24T03:36:25.042006+00:00
-- url     : https://prove2.me/theorems/e00fc4bb-9dce-47ff-8776-bd8d33197e68
-- statement:
--   Nisan block sensitivity `bs(f)`: maximum number of pairwise-disjoint sensitive blocks.

import Definitions.Def_BoolFunc
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi

/-!
# Block sensitivity of a Boolean function

Nisan block sensitivity: the pointwise version `bs(f, x)` is the maximum
number of pairwise-disjoint *sensitive blocks* at `x`, and `bs(f)` is its
global maximum.

The definition uses `Finset.sup` over a provably-finite `Finset` of candidate
block-families, so the max is the honest maximum (no `sSup`-returns-0-on-
unbounded pathology).
-/

/-- Flip every bit of `x` whose index lies in `B`. -/
def flipBlock {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !x i else x i

/-- `B` is a sensitive block for `f` at `x`: nonempty and flipping it changes `f x`. -/
def IsSensitiveBlock {n : ℕ} (f : BoolFunc n) (x : Fin n → Bool)
    (B : Finset (Fin n)) : Prop :=
  B.Nonempty ∧ f (flipBlock x B) ≠ f x

open Classical in
/-- All families of pairwise-disjoint sensitive blocks at `x`, as a `Finset`. -/
noncomputable def sensitiveBlockFamilies {n : ℕ} (f : BoolFunc n)
    (x : Fin n → Bool) : Finset (Finset (Finset (Fin n))) :=
  (Finset.univ : Finset (Finset (Finset (Fin n)))).filter fun 𝓑 =>
    (∀ B ∈ 𝓑, IsSensitiveBlock f x B)
      ∧ (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id

/-- Pointwise block sensitivity `bs(f, x)`: maximum size of a pairwise-disjoint
    family of sensitive blocks at `x`. -/
noncomputable def blockSensitivityAt {n : ℕ} (f : BoolFunc n)
    (x : Fin n → Bool) : ℕ :=
  (sensitiveBlockFamilies f x).sup Finset.card

/-- Block sensitivity `bs(f)`: maximum of pointwise block sensitivity. -/
noncomputable def blockSensitivity {n : ℕ} (f : BoolFunc n) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)


