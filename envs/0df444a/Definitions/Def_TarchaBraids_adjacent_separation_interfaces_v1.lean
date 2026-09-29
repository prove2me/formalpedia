-- Prove2me | Definitions.Def_TarchaBraids_adjacent_separation_interfaces_v1
-- name    : TarchaBraids_adjacent_separation_interfaces_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T08:43:57.640059+00:00
-- url     : https://prove2.me/theorems/a7c7d4f9-f7fa-4ede-91ea-670015687331
-- title:
--   Tarcha adjacent left interpolation separation interfaces
-- statement:
--   Named proposition structures for pairwise separation of the three local interpolation strands and their separation from every nonlocal strand.
-- source:
--   Modular separation interface extracted from the explicit adjacent Artin relation interpolation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

structure AdjacentLeftPairwiseSeparationFacts {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : Prop where
  local01_ne : ∀ (u q : ℝ),
    0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
    leftOuterInterpFun n i j u q (strandIdx i) ≠
      leftOuterInterpFun n i j u q (strandIdxSucc i)
  local02_ne : ∀ (u q : ℝ),
    0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
    leftOuterInterpFun n i j u q (strandIdx i) ≠
      leftOuterInterpFun n i j u q (strandIdxSucc j)
  local12_ne : ∀ (u q : ℝ),
    0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
    leftOuterInterpFun n i j u q (strandIdxSucc i) ≠
      leftOuterInterpFun n i j u q (strandIdxSucc j)

structure AdjacentLeftOutsideSeparationFacts {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : Prop where
  a_ne_outside : ∀ (u q : ℝ),
    0 ≤ u → u ≤ 1 →
    ∀ (k : Fin n),
      (k : ℕ) ≠ (i : ℕ) →
      (k : ℕ) ≠ (i : ℕ) + 1 →
      (k : ℕ) ≠ (i : ℕ) + 2 →
      leftOuterInterpFun n i j u q (strandIdx i) ≠
        leftOuterInterpFun n i j u q k
  b_ne_outside : ∀ (u q : ℝ),
    0 ≤ u → u ≤ 1 →
    ∀ (k : Fin n),
      (k : ℕ) ≠ (i : ℕ) →
      (k : ℕ) ≠ (i : ℕ) + 1 →
      (k : ℕ) ≠ (i : ℕ) + 2 →
      leftOuterInterpFun n i j u q (strandIdxSucc i) ≠
        leftOuterInterpFun n i j u q k
  c_ne_outside : ∀ (u q : ℝ),
    0 ≤ u → u ≤ 1 →
    ∀ (k : Fin n),
      (k : ℕ) ≠ (i : ℕ) →
      (k : ℕ) ≠ (i : ℕ) + 1 →
      (k : ℕ) ≠ (i : ℕ) + 2 →
      leftOuterInterpFun n i j u q (strandIdxSucc j) ≠
        leftOuterInterpFun n i j u q k

end TarchaBraids


