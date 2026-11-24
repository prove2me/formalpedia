-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotIdentity
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:16.441126+00:00
-- url     : https://prove2.me/theorems/caa74c6e-1ccc-40f1-b605-65ad9206c7a9
-- title:
--   PFlag Pivot Identity
-- statement:
--   Definitions and structural lemmas for PFlag Pivot Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotIdentity.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagPivotIdentity
variable {R : Type} [CommRing R] {n : ℕ}
def leadDet (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0
def pivotCof (M : Matrix (Fin n) (Fin n) R) {a : ℕ} (ha : a + 1 ≤ n) (i : Fin (a + 1)) : R :=
  (-1) ^ ((i : ℕ) + a) * (M.submatrix (Fin.castLE ha ∘ i.succAbove) (Fin.castLE (by omega))).det
def pivotCoeff (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) R :=
  Matrix.of fun a i =>
    if h : (i : ℕ) ≤ a then pivotCof M (a := a) (by have := j.2; have := a.2; omega) ⟨i, by omega⟩ else 0
end FlagPivotIdentity
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


