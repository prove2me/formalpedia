-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagPivot
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_FlagPivot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:46.62293+00:00
-- url     : https://prove2.me/theorems/6d0b6dff-37f0-4df0-96ae-97c9e0bd6c41
-- title:
--   Flag Pivot
-- statement:
--   Definitions and structural lemmas for Flag Pivot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FlagPivot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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
open MvPolynomial
def pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) : Fin (a + 1) → Fin n :=
  fun c => if h : (c : ℕ) < a then ⟨c, by have := a.2; omega⟩ else b
def pivotMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) : R :=
  (M.submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)).det
def leadMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) : R :=
  pivotMinor M a (Fin.castLE (Nat.sub_le n 1) a)
def pivotMatrix {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r b => if h : (r : ℕ) < n - 1 then pivotMinor M ⟨r, h⟩ b else 0
theorem pivotCols_strictMono {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    StrictMono (pivotCols a b) := by
  intro c d hcd
  have hcd' : (c : ℕ) < d := hcd
  simp only [pivotCols]
  split_ifs with h1 h2 h2
  · exact Fin.mk_lt_mk.mpr hcd'
  · exact Fin.mk_lt_mk.mpr (by omega)
  · omega
  · omega
theorem card_image_pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    (Finset.univ.image (pivotCols a b)).card = a + 1 := by
  rw [Finset.card_image_of_injective _ (pivotCols_strictMono a b hab).injective, Finset.card_univ, Fintype.card_fin]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


