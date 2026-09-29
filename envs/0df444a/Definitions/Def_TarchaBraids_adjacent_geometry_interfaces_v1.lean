-- Prove2me | Definitions.Def_TarchaBraids_adjacent_geometry_interfaces_v1
-- name    : TarchaBraids_adjacent_geometry_interfaces_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T08:36:32.057413+00:00
-- url     : https://prove2.me/theorems/3f9bf15e-31ab-4097-a434-4ad2459442aa
-- title:
--   Tarcha adjacent braid local geometry interfaces
-- statement:
--   Named proposition structures collecting the local strand-value and outside-strand identities used by the explicit adjacent Artin relation interpolation proof.
-- source:
--   Modular interface extraction from the explicit geometric proof of Tarcha's adjacent Artin braid relation.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

structure AdjacentLeftLocalFacts {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : Prop where
  first_a : ∀ q : ℝ, q ≤ 1 / 2 →
    leftBraidFun n i j q (strandIdx i) =
      twistPoint ((i : ℕ) + 3 / 2) (-1) (2 * q)
  first_b : ∀ q : ℝ, q ≤ 1 / 2 →
    leftBraidFun n i j q (strandIdxSucc i) =
      twistPoint ((i : ℕ) + 3 / 2) 1 (2 * q)
  first_c : ∀ q : ℝ, q ≤ 1 / 2 →
    leftBraidFun n i j q (strandIdxSucc j) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ)
  middle_a : ∀ q : ℝ, ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
    leftBraidFun n i j q (strandIdx i) =
      twistPoint ((i : ℕ) + 5 / 2) (-1) (4 * q - 2)
  middle_b : ∀ q : ℝ, ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
    leftBraidFun n i j q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ)
  middle_c : ∀ q : ℝ, ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
    leftBraidFun n i j q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 5 / 2) 1 (4 * q - 2)
  final_a : ∀ q : ℝ, ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
    leftBraidFun n i j q (strandIdx i) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ)
  final_b : ∀ q : ℝ, ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
    leftBraidFun n i j q (strandIdxSucc i) =
      twistPoint ((i : ℕ) + 3 / 2) (-1) (4 * q - 3)
  final_c : ∀ q : ℝ, ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
    leftBraidFun n i j q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 3 / 2) 1 (4 * q - 3)

structure AdjacentOuterOutsideFacts {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : Prop where
  outer_a : ∀ q : ℝ,
    outerRotateFun n i q (strandIdx i) =
      twistPoint ((i : ℕ) + 2) (-2) q
  outer_b : ∀ q : ℝ,
    outerRotateFun n i q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 2 : ℝ) : ℂ)
  outer_c : ∀ q : ℝ,
    outerRotateFun n i q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 2) 2 q
  left_outside : ∀ (q : ℝ) (k : Fin n),
    (k : ℕ) ≠ (i : ℕ) →
    (k : ℕ) ≠ (i : ℕ) + 1 →
    (k : ℕ) ≠ (i : ℕ) + 2 →
    leftBraidFun n i j q k = (((k : ℕ) + 1 : ℝ) : ℂ)
  right_outside : ∀ (q : ℝ) (k : Fin n),
    (k : ℕ) ≠ (i : ℕ) →
    (k : ℕ) ≠ (i : ℕ) + 1 →
    (k : ℕ) ≠ (i : ℕ) + 2 →
    rightBraidFun n i j q k = (((k : ℕ) + 1 : ℝ) : ℂ)
  outer_outside : ∀ (q : ℝ) (k : Fin n),
    (k : ℕ) ≠ (i : ℕ) →
    (k : ℕ) ≠ (i : ℕ) + 1 →
    (k : ℕ) ≠ (i : ℕ) + 2 →
    outerRotateFun n i q k = (((k : ℕ) + 1 : ℝ) : ℂ)

end TarchaBraids


