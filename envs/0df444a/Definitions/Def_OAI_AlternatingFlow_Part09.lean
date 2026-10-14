-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part09
-- name    : OAI_AlternatingFlow_Part09
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:44:42.676604+00:00
-- url     : https://prove2.me/theorems/e0d45f33-defe-40eb-bcc8-230dc1080324
-- title:
--   Alternating-flow construction, part 9 of 11 (port of OpenAI's formalization): mixed programs
-- statement:
--   Part 9 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains mixed programs.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `MixedPrograms` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/MixedPrograms.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 9 of 11: mixed programs.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: MixedPrograms.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part08

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/MixedPrograms.lean =====
namespace OAI

section MixedProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma wordJet_linear {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (w : List (Fin 4)) :
    wordJet (L ∘ f) w = L ∘ wordJet f w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext z
    simp only [wordJet, ih]
    rw [fderiv_comp _ L.differentiableAt ((wordJet_smooth hf w).differentiable (by simp) z), L.fderiv]
    rfl

lemma wordJet_component {f : ℝ × Space → Space} (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (w : List (Fin 4)) :
    wordJet (fun z => f z i) w = fun z => wordJet f w z i :=
  wordJet_linear hf (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i) w

lemma JetBound.named_component_words {f : A → ℝ × Space → Space} (hf : JetBound f)
    (hn : Named (fun z : (A × Fin 3) × RationalPoint => f z.1.1 (rationalPoint z.2) z.1.2)) :
    Named (fun z : ((A × Fin 3) × List (Fin 4)) × RationalPoint =>
      wordJet (f z.1.1.1) z.1.2 (rationalPoint z.2) z.1.1.2) := by
  have hp := (hf.param (Computable.fst : Computable (Prod.fst : A × Fin 3 → A))).linear_unit
    (fun p => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) p.2) (fun p => norm_proj p.2)
  exact (hp.named_wordJet hn).congr (fun z => congrFun (wordJet_component (hf.1 z.1.1.1) z.1.1.2 z.1.2) (rationalPoint z.2))

lemma wordJet_append (f : ℝ × Space → E) (v w : List (Fin 4)) :
    wordJet f (v ++ w) = wordJet (wordJet f w) v := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append, wordJet, ih]

lemma wordJet_dx (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (i : Fin 3) (n : ℕ) :
    Function.uncurry ((dx i)^[n] f) = wordJet (Function.uncurry f) (List.replicate n i.succ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext z
    rw [Function.iterate_succ_apply']
    change dx i ((dx i)^[n] f) z.1 z.2 = _
    rw [Bounds.dx_eq_full_directional _ (Analytic.iterate_dx_smooth f hf i n), ih]
    simp only [List.replicate_succ, wordJet, direction_succ]

lemma wordJet_dt (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    Bounds.HalfEq (dt^[n] f) (fun t x => wordJet (Function.uncurry f) (List.replicate n 0) (t,x)) := by
  induction n with
  | zero => exact fun _ _ _ => rfl
  | succ n ih =>
    intro t ht x
    rw [Function.iterate_succ_apply']
    have hh := ih.dt t ht x
    have hs := wordJet_smooth hf (List.replicate n 0)
    rw [Analytic.dt_eq_full (fun t x => wordJet (Function.uncurry f) (List.replicate n 0) (t,x)) hs t ht x,
      Bounds.fullDt_eq_full_directional (fun t x => wordJet (Function.uncurry f) (List.replicate n 0) (t,x)) hs (t,x)] at hh
    change dt (dt^[n] f) t x = fderiv ℝ (wordJet (Function.uncurry f) (List.replicate n 0)) (t,x) (1,0) at hh
    simpa only [List.replicate_succ, wordJet, direction, Matrix.cons_val_zero] using hh

def mixedWord (l : ℕ) (α : IndexCode) : List (Fin 4) :=
  List.replicate l 0 ++ (List.replicate α.1 1 ++
    (List.replicate α.2.1 2 ++ List.replicate α.2.2 3))

lemma wordJet_spatial (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (α : IndexCode) :
    Function.uncurry (spatial (index α) f) =
      wordJet (Function.uncurry f) (List.replicate α.1 1 ++
        (List.replicate α.2.1 2 ++ List.replicate α.2.2 3)) := by
  simp only [spatial, index, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [wordJet_dx _ (Analytic.iterate_dx_smooth _ (Analytic.iterate_dx_smooth f hf 2 _) 1 _),
    wordJet_dx _ (Analytic.iterate_dx_smooth f hf 2 _), wordJet_dx f hf]
  simp only [wordJet_append]
  rfl

lemma mixed_eq_wordJet (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (l : ℕ) (α : IndexCode) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    mixed l (index α) f t x = wordJet (Function.uncurry f) (mixedWord l α) (t,x) := by
  have h := wordJet_dt (spatial (index α) f) (Analytic.spatial_smooth f hf _) l t ht x
  rw [wordJet_spatial f hf α] at h
  simpa only [mixedWord, wordJet_append, mixed] using h

lemma replicate_primrec {B : Type*} [Primcodable B] (b : B) : Primrec (fun n => List.replicate n b) := by
  have h := Primrec.nat_rec₁ (f := fun _ : ℕ => fun w : List B => b :: w) ([] : List B)
    (Primrec.list_cons.comp (Primrec.const b) Primrec.snd)
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change b :: _ = List.replicate (n+1) b
    rw [ih, List.replicate_succ]

lemma mixedWord_computable : Computable₂ mixedWord := by
  have hr (i : Fin 4) := (replicate_primrec i).to_comp
  exact Primrec.list_append.to_comp.comp ((hr 0).comp Computable.fst)
    (Primrec.list_append.to_comp.comp ((hr 1).comp (Computable.fst.comp Computable.snd))
      (Primrec.list_append.to_comp.comp ((hr 2).comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
        ((hr 3).comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))))

end AlternatingNS.Effective

end MixedProgramsDevelopment

end OAI


