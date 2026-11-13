-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
-- name    : OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:54:08.080759+00:00
-- url     : https://prove2.me/theorems/7e2587e8-c83a-4c83-9dd4-b22939109df1
-- title:
--   Peterfalvi (7.10): the Frobenius family, character-estimate target (tail)
-- statement:
--   The final part of the Peterfalvi §7 Frobenius-family development.
--
--   The main structure is `CharacterEstimateData`, the (7.10) character-estimate target.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/FrobeniusFamily.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/FrobeniusFamily.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CharacterEstimate

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace FrobeniusFamily

variable {k : ℕ}

/-- **Peterfalvi (7.10) character-estimate target.**  This is the exact data
still to be built from the character-theoretic inputs (7.5), (7.8), (7.9), and
(6.8): a minimal kernel index, the corresponding `𝓑`-set, the unweighted
`𝓑`-sum bound, and the base estimate before the final arithmetic rearrangement.

It is standalone target data, not a field of `FrobeniusFamily`. -/
structure CharacterEstimateData [Finite G] (F : FrobeniusFamily G k) where
  /-- The index with minimal kernel order. -/
  i : Fin k
  /-- Minimality of `h_i`. -/
  hmin : ∀ l : Fin k, F.h i ≤ F.h l
  /-- The Peterfalvi `𝓑`-set of non-minimal indices. -/
  B : Finset (Fin k)
  /-- The chosen `𝓑`-indices avoid the minimal index. -/
  B_avoids_min : ∀ j ∈ B, i ≠ j
  /-- The unweighted `𝓑`-sum bound coming from (7.8.b) and (7.9). -/
  Bsum_le :
    (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1
  /-- The base estimate isolated from (7.5), before bounding the `𝓑`-sum. -/
  base_estimate :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ)))

end FrobeniusFamily

end OddOrder.Peterfalvi.S09


