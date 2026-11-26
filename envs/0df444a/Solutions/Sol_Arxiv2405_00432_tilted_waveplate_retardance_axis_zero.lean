-- Prove2me | solution 1 for Arxiv2405_00432.tilted_waveplate_retardance_axis_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:50:55.982077+00:00
-- url     : https://prove2.me/submissions/4f8826bc-7b1f-466f-9560-60a6cf14dbbb

import Definitions.Def_Arxiv2405_00432_Basic
import Mathlib
import Mathlib.Tactic


open Matrix
namespace Arxiv2405_00432

theorem _root_.solution (T lam no ne α : ℝ) (hT : 0 < T) (hlam : 0 < lam)
    (hno : 0 < no) (hne : 0 < ne) :
    theoryRetardance T lam no ne 0 α =
      2 * Real.pi * T / lam *
        (Real.sqrt (ne ^ 2 * (1 - Real.sin α ^ 2 / no ^ 2)) - Real.sqrt (no ^ 2 - Real.sin α ^ 2)) := by
  first
    | (intros; rfl)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp [theoryRetardance]; done)
    | (intros; grind)
    | (intros; grind [theoryRetardance])
    | (intros; unfold theoryRetardance; grind)
    | (intros; simp only [theoryRetardance] at * <;> grind)
    | (intros; simp_all [theoryRetardance] <;> grind)
    | (intros; ext <;> grind [theoryRetardance])
    | (intros; constructor <;> intro _ <;> grind [theoryRetardance])
    | (intro x; cases x <;> grind [theoryRetardance])
    | (intro x; induction x <;> simp_all [theoryRetardance])
    | (intro x y; induction x <;> grind [theoryRetardance])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [theoryRetardance])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [theoryRetardance])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_9_3"


end Arxiv2405_00432
