-- Prove2me | solution 1 for AlliancePortfolio.Sharing.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:25:26.820535+00:00
-- url     : https://prove2.me/submissions/e67b9fa7-9f2a-478e-b8fc-9edfeb4f1705

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open AlliancePortfolio.Sharing

theorem ww_phiF (V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB F = V + πF + b / 3 + (sImp - sRB) / 3 := by
  have hF : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  have hp : ({1, 2} : Finset (Fin 3)).powerset = {∅, {1}, {2}, {1, 2}} := by decide
  simp only [φ, Supermodularity.Cooperative.ShapleyValue, F, hF, hp]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp (config := {decide := true}) [game, F, A, B, Nat.factorial]
  ring

theorem ww_phiA (V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB A = (1 / 2) * (V - πF) + (1 / 3) * b - (1 / 6) * (sImp - sRB) := by
  have hA : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have hpA : ({0, 2} : Finset (Fin 3)).powerset = {∅, {0}, {2}, {0, 2}} := by decide
  simp only [φ, Supermodularity.Cooperative.ShapleyValue, A, hA, hpA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp (config := {decide := true}) [game, F, A, B, Nat.factorial]
  ring

theorem ww_phiB (V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB B = (1 / 2) * (V - πF) + (1 / 3) * b - (1 / 6) * (sImp - sRB) := by
  have hB : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  have hpB : ({0, 1} : Finset (Fin 3)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  simp only [φ, Supermodularity.Cooperative.ShapleyValue, B, hB, hpB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp (config := {decide := true}) [game, F, A, B, Nat.factorial]
  ring

theorem solution (V I b πF sImp sRB : ℝ) (hstd : Standing V I b πF sImp sRB) (hVI : I ≤ V)
    (hlo : πF - (2 / 3) * b + (1 / 3) * (sImp - sRB) ≤ V - I) (hhi : V - I < πF) :
    PortfolioFeasible V I b πF sImp sRB ∧ ¬ SingleFeasible V I πF 0 := by
  obtain ⟨hI, hb, hs, hs2, hr, hr2⟩ := hstd
  have h0 : netPayoff V I b πF sImp sRB 0 = φ V b πF sImp sRB F - I := by
    simp [netPayoff, F]
  have h1 : netPayoff V I b πF sImp sRB 1 = φ V b πF sImp sRB A - (1 / 2) * I := by
    simp [netPayoff, F, A]
  have h2 : netPayoff V I b πF sImp sRB 2 = φ V b πF sImp sRB B - (1 / 2) * I := by
    simp [netPayoff, F, B]
  constructor
  · intro i
    fin_cases i
    · show 0 ≤ netPayoff V I b πF sImp sRB 0
      rw [h0, ww_phiF]; linarith
    · show 0 ≤ netPayoff V I b πF sImp sRB 1
      rw [h1]; change 0 ≤ φ V b πF sImp sRB A - (1 / 2) * I
      rw [ww_phiA]; linarith
    · show 0 ≤ netPayoff V I b πF sImp sRB 2
      rw [h2]; change 0 ≤ φ V b πF sImp sRB B - (1 / 2) * I
      rw [ww_phiB]; linarith
  · intro h
    have := h.2
    unfold singlePayoff at this
    linarith
