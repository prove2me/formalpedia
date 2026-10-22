-- Prove2me | solution 1 for AlliancePortfolio.Sharing.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:12:10.670873+00:00
-- url     : https://prove2.me/submissions/b58e8b19-64c2-4244-8bcf-e6a807c1dc2c

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open AlliancePortfolio.Sharing

theorem solution (V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB A = (1 / 2) * (V - πF) + (1 / 3) * b - (1 / 6) * (sImp - sRB) ∧
      φ V b πF sImp sRB B = (1 / 2) * (V - πF) + (1 / 3) * b - (1 / 6) * (sImp - sRB) := by
  have hA : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have hB : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  have hpA : ({0, 2} : Finset (Fin 3)).powerset = {∅, {0}, {2}, {0, 2}} := by decide
  have hpB : ({0, 1} : Finset (Fin 3)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  constructor
  · simp only [φ, Supermodularity.Cooperative.ShapleyValue, A, hA, hpA]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp (config := {decide := true}) [game, F, A, B, Nat.factorial]
    ring
  · simp only [φ, Supermodularity.Cooperative.ShapleyValue, B, hB, hpB]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp (config := {decide := true}) [game, F, A, B, Nat.factorial]
    ring
