-- Prove2me | solution 1 for Arxiv1810_02867.unified_form_table1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:58:21.662431+00:00
-- url     : https://prove2.me/submissions/4bb1b3b8-11d3-4d2a-b0d8-ff30ef78f9bb

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

set_option autoImplicit false

open MeasureTheory Matrix

namespace S71UT
open Arxiv1810_02867

lemma pdx_neg {n : ℕ} (r : Fin n) (f : (Fin n → ℝ) → ℝ → ℝ) (x : Fin n → ℝ) (t : ℝ) :
    pdx r (fun y s => -f y s) x t = -pdx r f x t := by
  unfold pdx pd; exact deriv.neg

lemma pdt_neg {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) (x : Fin n → ℝ) (t : ℝ) :
    pdt (fun y s => -f y s) x t = -pdt f x t := by
  unfold pdt; exact deriv.neg

end S71UT

open Arxiv1810_02867 S71UT in
theorem solution :
    (∀ (eO xi mu : Plane → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Plane → ℝ → Fin 3 → ℝ),
      TESystem eO xi mu E H Je Jm ↔
        UnifiedEqs (fun x => eO x 1 1)
          (fun x => ![![mu x 2 2, -mu x 2 0], ![-mu x 2 0, mu x 0 0]])
          (fun x => ![xi x 1 2, -xi x 1 0]) (cmp E 1) (fun x t => ![H x t 2, -H x t 0])
          (fun x t => -Je x t 1) (fun x t => ![-Jm x t 2, Jm x t 0])) ∧
    (∀ (eO xi mu : Plane → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Plane → ℝ → Fin 3 → ℝ),
      TMSystem eO xi mu E H Je Jm ↔
        UnifiedEqs (fun x => mu x 1 1)
          (fun x => ![![eO x 2 2, -eO x 2 0], ![-eO x 2 0, eO x 0 0]])
          (fun x => ![-xi x 2 1, xi x 0 1]) (cmp H 1) (fun x t => ![-E x t 2, E x t 0])
          (fun x t => -Jm x t 1) (fun x t => ![Je x t 2, -Je x t 0])) ∧
    (∀ (rhoO : Plane → Fin 3 → Fin 3 → ℝ) (xi : Plane → Fin 3 → Fin 3 → Fin 3 → ℝ)
        (s : Plane → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v F : Plane → ℝ → Fin 3 → ℝ)
        (tau h : Plane → ℝ → Fin 3 → Fin 3 → ℝ),
      SHSystem rhoO xi s v tau F h ↔
        UnifiedEqs (fun x => rhoO x 1 1)
          (fun x => ![![4 * s x 0 1 1 0, 4 * s x 0 1 1 2], ![4 * s x 0 1 1 2, 4 * s x 2 1 1 2]])
          (fun x => ![2 * xi x 1 1 0, 2 * xi x 1 1 2]) (cmp v 1)
          (fun x t => ![-tau x t 1 0, -tau x t 1 2]) (cmp F 1)
          (fun x t => ![2 * h x t 1 0, 2 * h x t 1 2])) ∧
    (∀ (rhoO : Plane → Fin 3 → Fin 3 → ℝ) (xi : Plane → Fin 3 → ℝ) (kappa : Plane → ℝ)
        (v F : Plane → ℝ → Fin 3 → ℝ) (pr q : Plane → ℝ → ℝ),
      ACSystem rhoO xi kappa v pr F q ↔
        UnifiedEqs kappa (fun x => ![![rhoO x 0 0, rhoO x 2 0], ![rhoO x 2 0, rhoO x 2 2]])
          (fun x => ![xi x 0, xi x 2]) pr (fun x t => ![v x t 0, v x t 2]) q
          (fun x t => ![F x t 0, F x t 2])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp only [TESystem, TMSystem, SHSystem, ACSystem, UnifiedEqs, Dg]
    unfold Arxiv1810_02867.cmp
    simp only [Fin.sum_univ_two, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
    try simp only [pdx_neg, pdt_neg]
    refine forall_congr' fun x => forall_congr' fun t => ?_
    constructor
    · rintro ⟨a, b, c⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨a, b, c⟩
      exact ⟨by linarith, by linarith, by linarith⟩
