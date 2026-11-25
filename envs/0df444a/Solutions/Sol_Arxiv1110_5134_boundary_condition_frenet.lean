-- Prove2me | solution 1 for Arxiv1110_5134.boundary_condition_frenet
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:42.134698+00:00
-- url     : https://prove2.me/submissions/5d7878d1-c9dd-4a84-a2df-4f231837248f

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic
import Theorems.Thm_Arxiv1110_5134_fixed_frame_rotation
import Theorems.Thm_Arxiv1110_5134_stokes_right_to_left_hand

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (σ φ : ℝ) (hσ : σ ≠ 0) (I IG IGLF : Stokes)
    (h30 : IG = modRot σ φ *ᵥ I) :
    I = modRot σ (-φ) *ᵥ IG ∧
    (IGLF = handT *ᵥ IG → I = modRot σ (-φ) *ᵥ (handT *ᵥ IGLF)) := by
  have h1 : I = modRot σ (-φ) *ᵥ IG :=
    ((fixed_frame_rotation σ φ).2.2.2.2 hσ I IG).mp h30
  refine ⟨h1, ?_⟩
  intro hLF
  have hTT : handT * handT = 1 := (stokes_right_to_left_hand 0 0 0 0).2.2
  have h2 : handT *ᵥ IGLF = IG := by
    rw [hLF, Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec]
  rw [h2]
  exact h1
