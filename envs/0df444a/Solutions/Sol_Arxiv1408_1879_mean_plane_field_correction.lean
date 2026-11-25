-- Prove2me | solution 1 for Arxiv1408_1879.mean_plane_field_correction
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:36:51.925283+00:00
-- url     : https://prove2.me/submissions/1042b40e-0f5e-4db2-a68a-0e08d238f1b6

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace Arxiv1408_1879

theorem mean_plane_field_correction (ψi : ℝ → ℝ → ℂ) (h : ℝ → ℝ) (ψt C : ℝ → ℂ) (x : ℝ) :
    meanPlaneField ψi h (fun s => ψt s - C s) x = meanPlaneField ψi h ψt x + (h x : ℂ) * C x := by
  simp only [meanPlaneField]; ring

end Arxiv1408_1879
open Arxiv1408_1879 in
theorem solution (ψi : ℝ → ℝ → ℂ) (h : ℝ → ℝ) (ψt C : ℝ → ℂ) (x : ℝ) :
    meanPlaneField ψi h (fun s => ψt s - C s) x = meanPlaneField ψi h ψt x + (h x : ℂ) * C x :=
  mean_plane_field_correction ψi h ψt C x
