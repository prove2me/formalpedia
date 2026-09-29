-- Prove2me | solution 1 for AutomorphicForm.contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f1560fad-9249-595c-868a-58135f1b9270

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

noncomputable section

namespace P2M
namespace ArchBridge

open Matrix

variable {F : Type} [Field F] [NumberField F]

theorem mapMatrix_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    f.mapMatrix ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = ((unipotentGL2 (f x) : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

theorem coe_glFin (x : AdelicGL2 (𝓞 F) F) :
    ((glFin (𝓞 F) F x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = (adeleFin (𝓞 F) F).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j
  rw [glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply]

theorem coe_glArch (x : AdelicGL2 (𝓞 F) F) :
    ((glArch (𝓞 F) F x : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      = (adeleArch (𝓞 F) F).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j
  rw [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]

theorem coe_archComponent (w : InfinitePlace F) (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((archComponent F w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = (archEval F w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  ext i j
  rw [archComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem eq_of_forall_archComponent_eq {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y := by
  apply Units.ext
  ext i j
  funext w
  have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)
  rwa [archComponent_apply, archComponent_apply] at this

theorem glFin_unipotentGL2_arch (x : InfiniteAdeleRing F) :
    glFin (𝓞 F) F (unipotentGL2 ((x, 0) : AdeleRing (𝓞 F) F)) = 1 := by
  apply Units.ext
  rw [coe_glFin, mapMatrix_unipotentGL2, Units.val_one]
  rw [show adeleFin (𝓞 F) F ((x, 0) : AdeleRing (𝓞 F) F) = 0 from rfl, unipotentGL2_zero, Units.val_one]

theorem glArch_unipotentGL2_arch (x : InfiniteAdeleRing F) :
    glArch (𝓞 F) F (unipotentGL2 ((x, 0) : AdeleRing (𝓞 F) F)) = unipotentGL2 x := by
  apply Units.ext
  rw [coe_glArch, mapMatrix_unipotentGL2]
  rfl

theorem archComponent_unipotentGL2 (w : InfinitePlace F) (x : InfiniteAdeleRing F) :
    archComponent F w (unipotentGL2 x) = unipotentGL2 (x w) := by
  apply Units.ext
  rw [coe_archComponent, mapMatrix_unipotentGL2]
  rfl

theorem inv_mul_adelicArchGLIncl_mul (g : AdelicGL2 (𝓞 F) F) (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    g⁻¹ * adelicArchGLIncl F k * g = adelicArchGLIncl F ((glArch (𝓞 F) F g)⁻¹ * k * glArch (𝓞 F) F g) := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, map_inv, glArch_adelicArchGLIncl, glArch_adelicArchGLIncl]
  · rw [map_mul, map_mul, map_inv, glFin_adelicArchGLIncl, glFin_adelicArchGLIncl, mul_one, inv_mul_cancel]

end P2M.ArchBridge

end

open P2M.ArchBridge in
open scoped Classical in
theorem solution
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt Rat.isReal_infinitePlace φ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ (Module.finrank ℚ ℚ + 1) (fun z : mixedEmbedding.mixedSpace ℚ =>
      φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z, 0) * g)) := by
  set w : InfinitePlace ℚ := Rat.infinitePlace with hwdef
  have hw : w.IsReal := Rat.isReal_infinitePlace

  have hT0 : ∀ z : mixedEmbedding.mixedSpace ℚ, (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z) w) = z.1 ⟨w, hw⟩ := by
    intro z
    have h := congrArg (fun p : mixedEmbedding.mixedSpace ℚ => p.1 ⟨w, hw⟩)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).apply_symm_apply z)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact h

  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      A = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.mapMatrix (((archComponent ℚ w (glArch (𝓞 ℚ) ℚ g))⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin 2) (Fin 2) ℝ,
      B = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.mapMatrix (((archComponent ℚ w (glArch (𝓞 ℚ) ℚ g)) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ → (Fin 2 → Fin 2 → ℝ),
      P = fun t i j => (A * ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * B) i j := ⟨_, rfl⟩
  have hPsmooth : ContDiff ℝ (⊤ : ℕ∞) P := by
    rw [hP]
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe] <;> fun_prop
  have hTsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : mixedEmbedding.mixedSpace ℚ => z.1 ⟨w, hw⟩) := by fun_prop

  obtain ⟨k, hk⟩ : ∃ k : mixedEmbedding.mixedSpace ℚ → GL (Fin 2) w.Completion,
      k = fun z => (archComponent ℚ w (glArch (𝓞 ℚ) ℚ g))⁻¹ * unipotentGL2 (((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z) w) * (archComponent ℚ w (glArch (𝓞 ℚ) ℚ g)) := ⟨_, rfl⟩
  have hkP : ∀ z, ((glEquivOfRingEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (k z) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.of (P (z.1 ⟨w, hw⟩)) := by
    intro z
    have h1 : Matrix.of (P (z.1 ⟨w, hw⟩))
        = A * ((unipotentGL2 (z.1 ⟨w, hw⟩) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * B := by
      ext i j; rw [Matrix.of_apply, hP]
    have h2 : ((unipotentGL2 (z.1 ⟨w, hw⟩) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.mapMatrix
            ((unipotentGL2 (((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z) w) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
      rw [mapMatrix_unipotentGL2, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hT0 z]
    rw [h1, h2, hA, hB, ← map_mul, ← map_mul, hk]
    ext i j
    rw [glEquivOfRingEquiv_apply_entry, RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_mul, Units.val_mul]
    rfl
  have hdet : ∀ z : mixedEmbedding.mixedSpace ℚ, (Matrix.of (P (z.1 ⟨w, hw⟩))).det ≠ 0 := by
    intro z
    rw [← hkP z]
    exact (Matrix.isUnits_det_units _).ne_zero
  have hlift : ∀ z : mixedEmbedding.mixedSpace ℚ,
      archRealLiftAt hw (P (z.1 ⟨w, hw⟩)) = adelicArchGLInclAt ℚ w (k z) := by
    intro z
    rw [archRealLiftAt_of_det_ne_zero hw (hdet z), ← archRealGLAt_glEquivOfRingEquiv hw (k z)]
    congr 1
    apply Units.ext
    rw [hkP z]
    rfl

  have hkey : ∀ z : mixedEmbedding.mixedSpace ℚ,
      unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z), 0) * g = g * archRealLiftAt hw (P (z.1 ⟨w, hw⟩)) := by
    intro z
    have hn : unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z), 0) = adelicArchGLIncl ℚ (unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z)) := by
      refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
      · rw [glArch_unipotentGL2_arch, glArch_adelicArchGLIncl]
      · rw [glFin_unipotentGL2_arch, glFin_adelicArchGLIncl]
    have hconj : g⁻¹ * adelicArchGLIncl ℚ (unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z)) * g = adelicArchGLInclAt ℚ w (k z) := by
      rw [inv_mul_adelicArchGLIncl_mul]
      show adelicArchGLIncl ℚ _ = adelicArchGLIncl ℚ (archGLIncl ℚ w (k z))
      congr 1
      refine eq_of_forall_archComponent_eq fun v => ?_
      obtain rfl : v = w := Subsingleton.elim v w
      rw [archComponent_archGLIncl_self, map_mul, map_mul, map_inv, archComponent_unipotentGL2, hk]
    rw [hlift z, ← hconj, hn, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hfun : (fun z : mixedEmbedding.mixedSpace ℚ =>
      φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z), 0) * g))
      = (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e)) ∘ (fun z => P (z.1 ⟨w, hw⟩)) := by
    funext z
    simp only [Function.comp_apply, hkey z]
  rw [hfun]
  refine ((hsm g).of_le ?_).comp_contDiff ((hPsmooth.of_le ?_).comp (hTsmooth.of_le ?_)) fun z => hdet z
  all_goals exact_mod_cast le_top

end S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
end P2MW
export P2MW.S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat (solution)
