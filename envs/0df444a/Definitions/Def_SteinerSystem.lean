-- Prove2me | Definitions.Def_SteinerSystem
-- name    : SteinerSystem
-- status  : Definition
-- author  : @parclytaxel
-- created : 2026-11-11T05:56:06.503562+00:00
-- url     : https://prove2.me/theorems/f6d51a14-8673-4880-b4b6-17d810730c88
-- title:
--   Definition of Steiner systems
-- statement:
--   An $(n,k,t)$-Steiner system is a set of $k$-subsets (blocks) of an $n$-set such that every $t$-subset is contained in exactly one block.

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Finset

/-- A structure for a Steiner system on `n` points with size-`k` blocks
containing all `t`-subsets exactly once. -/
@[ext]
structure SteinerSystem (n k t : ℕ) where
  /-- Blocks of the system -/
  blocks : Finset (Finset (Fin n))
  /-- Each block is of size `k` -/
  sized (b) (mb : b ∈ blocks) : #b = k
  /-- Each `t`-subset is in exactly one block -/
  cover (c) (cc : #c = t) : ∃! b ∈ blocks, c ⊆ b
deriving DecidableEq


