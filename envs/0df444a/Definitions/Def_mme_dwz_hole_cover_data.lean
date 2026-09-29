-- Prove2me | Definitions.Def_mme_dwz_hole_cover_data
-- name    : mme_dwz_hole_cover_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T10:03:46.103059+00:00
-- url     : https://prove2.me/theorems/17dadf32-d32b-4a55-ac3d-2b1b6811ef80
-- title:
--   DWZ standard-form Hole Lemma: available-block interface
-- statement:
--   Record the finite interface used by the proof of the DWZ Hole
--   Lemma. An available-block shuffle supplies the permutations induced on the
--   available small Z-blocks and the exact uniform-fiber identity of Claim 5.10.
--   A broken block copy records precisely its non-hole available blocks, and its
--   non-hole fraction is their cardinality divided by the total block count. This
--   is the honest combinatorial part of Definitions 5.3-5.5; realizing it for an
--   actual standard-form TensorObj remains a separate tensor leaf.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Definitions 5.3-5.5 and Claims 5.8-5.10 (printed pp. 47-48).

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# The finite covering interface in the DWZ Hole Lemma

Definitions 5.2--5.5 attach a finite set of available small Z-blocks to a
standard-form tensor.  Claims 5.8--5.10 show that its shuffling group acts by
permutations and sends each fixed block uniformly over that finite set.

This module records exactly that finite interface.  It intentionally does not
pretend that an arbitrary `TensorObj` already has the required lower-level
block decomposition; connecting this interface to concrete CW component
tensors is a separate tensor-realization milestone.
-/

open Finset

namespace MME.DWZSquare

universe u v

/-- Claims 5.8--5.10, restricted to the available-small-Z-block universe used
by the probabilistic covering argument in Lemma 5.6. -/
structure AvailableBlockShuffle
    (Block : Type u) (Shuffle : Type v)
    [Fintype Block] [DecidableEq Block]
    [Fintype Shuffle] [DecidableEq Shuffle] where
  /-- The block permutation induced by a shuffle. -/
  move : Shuffle → Equiv.Perm Block
  /-- Claim 5.10 in exact finite-cardinality form. -/
  uniform_fiber : ∀ source target : Block,
    (univ.filter (fun g : Shuffle ↦ move g source = target)).card *
        Fintype.card Block =
      Fintype.card Shuffle

/-- Definition 5.5 at the level relevant to Lemma 5.6: a broken copy is
determined by which available small Z-blocks remain non-holes. -/
structure BrokenBlockCopy (Block : Type u) [Fintype Block] where
  nonholes : Finset Block

/-- Definition 5.5's fraction of non-holes. -/
noncomputable def nonholeFraction
    {Block : Type u} [Fintype Block]
    (copy : BrokenBlockCopy Block) : ℝ :=
  (copy.nonholes.card : ℝ) / (Fintype.card Block : ℝ)

end MME.DWZSquare


