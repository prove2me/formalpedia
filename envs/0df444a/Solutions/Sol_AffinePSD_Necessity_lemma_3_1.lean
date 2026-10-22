-- Prove2me | solution 1 for AffinePSD.Necessity.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:12.483619+00:00
-- url     : https://prove2.me/submissions/2357ccd0-9c43-4a9f-ba7e-b60a0c98ef94

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

set_option autoImplicit false
open AffinePSD.Necessity

theorem solution {d : ℕ} (u v : Mat d) (hu : PSD u) (hu' : ¬ PD u) (hv : PSD v)
    (hvu : PSD (u - v)) : PSD v ∧ ¬ PD v := by
  refine ⟨hv, fun hPD => hu' ?_⟩
  have h : (Matrix.of v + Matrix.of (u - v)).PosDef := hPD.add_posSemidef hvu
  have e : Matrix.of v + Matrix.of (u - v) = Matrix.of u := by
    ext i j; simp [Matrix.of_apply]
  rw [e] at h
  exact h
