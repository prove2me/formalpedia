-- Prove2me | solution 1 for AutomorphicForm.exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b5972186-e1d6-50a3-88d9-75129b770fc4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain NumberField.InfinitePlace.Completion NumberField.TateGlobal
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace WBPlumb

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

theorem glInf_ext {g h : GL (Fin 2) (InfiniteAdeleRing K)}
    (H : ∀ v : InfinitePlace K, archComponent K v g = archComponent K v h) : g = h :=
  Units.ext (Matrix.ext fun i j => funext fun v =>
    congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j) (H v))

theorem glArch_adelicArchGLInclAt (a : GL (Fin 2) w.Completion) :
    glArch (𝓞 K) K (adelicArchGLInclAt K w a) = archGLIncl K w a :=
  glArch_adelicArchGLIncl K _

theorem glFin_adelicArchGLInclAt (a : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (adelicArchGLInclAt K w a) = 1 :=
  glFin_adelicArchGLIncl K _

theorem archComponent_glArch_adelicArchGLInclAt_self (a : GL (Fin 2) w.Completion) :
    archComponent K w (glArch (𝓞 K) K (adelicArchGLInclAt K w a)) = a := by
  rw [glArch_adelicArchGLInclAt, archComponent_archGLIncl_self]

theorem archComponent_glArch_adelicArchGLInclAt_of_ne {v : InfinitePlace K} (hvw : v ≠ w) (a : GL (Fin 2) w.Completion) :
    archComponent K v (glArch (𝓞 K) K (adelicArchGLInclAt K w a)) = 1 := by
  rw [glArch_adelicArchGLInclAt, archComponent_archGLIncl_of_ne K hvw]

theorem adelicArchGLInclAt_apply (a : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt K w a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        (a : Matrix (Fin 2) (Fin 2) w.Completion)) v i j), (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) := rfl

theorem adelicArchGLInclAt_apply_fst_self (a : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w =
      (a : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [adelicArchGLInclAt_apply]
  simp

theorem adelicArchGLInclAt_apply_fst_of_ne (a : GL (Fin 2) w.Completion) (i j : Fin 2) {v : InfinitePlace K} (hvw : v ≠ w) :
    (((adelicArchGLInclAt K w a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 v =
      (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  rw [adelicArchGLInclAt_apply]
  simp [Function.update_of_ne hvw]

theorem adelicArchGLInclAt_apply_snd (a : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j := rfl

theorem mul_comm_of_archComponent_eq_one (a : GL (Fin 2) w.Completion) {x : AdelicGL2 (𝓞 K) K}
    (hx : archComponent K w (glArch (𝓞 K) K x) = 1) :
    adelicArchGLInclAt K w a * x = x * adelicArchGLInclAt K w a := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, glArch_adelicArchGLInclAt]
    refine glInf_ext fun v => ?_
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self, hx, mul_one, one_mul]
    · rw [archComponent_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_adelicArchGLInclAt, one_mul, mul_one]

theorem archComponent_glArch_inv_incl_mul (k : AdelicGL2 (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K ((adelicArchGLInclAt K w (archComponent K w (glArch (𝓞 K) K k)))⁻¹ * k)) = 1 := by
  rw [map_mul, map_mul, map_inv, map_inv, archComponent_glArch_adelicArchGLInclAt_self, inv_mul_cancel]

theorem circleGL2_apply (ζ : ℂˣ) (i j : Fin 2) :
    (circleGL2 ζ : Matrix (Fin 2) (Fin 2) ℂ) i j = !![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)] i j := rfl

theorem archCircleAt_eq (hw : w.IsComplex) (ζ : ℂˣ) :
    archCircleAt hw ζ = adelicArchGLInclAt K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (circleGL2 ζ)) := rfl

theorem extensionEmbedding_symm (hw : w.IsComplex) (z : ℂ) :
    extensionEmbedding w ((ringEquivComplexOfIsComplex hw).symm z) = z :=
  (ringEquivComplexOfIsComplex hw).apply_symm_apply z

theorem archCircleAt_mem_adelicBorel (hw : w.IsComplex) (ζ : ℂˣ) : archCircleAt hw ζ ∈ adelicBorel (𝓞 K) K := by
  rw [adelicBorel, mem_borelSubgroup_iff, archCircleAt_eq, adelicArchGLInclAt_apply]
  refine Prod.ext (funext fun v => ?_) ?_
  · show Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        ((glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (circleGL2 ζ) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) v 1 0 = 0
    by_cases hv : v = w
    · subst hv
      rw [Function.update_self, glEquivOfRingEquiv_apply_entry, circleGL2_apply]
      simp
    · rw [Function.update_of_ne hv]
      simp
  · show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0 = 0
    simp

theorem borelDiagFst_archCircleAt (hw : w.IsComplex) (ζ : ℂˣ) :
    borelDiagFst ⟨archCircleAt hw ζ, archCircleAt_mem_adelicBorel hw ζ⟩ =
      archUnitHom w (Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ) := by
  apply Units.ext
  show ((archCircleAt hw ζ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
    ((Function.update (1 : Π v : InfinitePlace K, v.Completion) w
      ((Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ : (w.Completion)ˣ) : w.Completion), 1) :
        AdeleRing (𝓞 K) K)
  rw [archCircleAt_eq, adelicArchGLInclAt_apply]
  refine Prod.ext (funext fun v => ?_) (by simp)
  show Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
      ((glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (circleGL2 ζ) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) v 0 0 =
    Function.update (1 : Π v : InfinitePlace K, v.Completion) w
      ((Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ : (w.Completion)ˣ) : w.Completion) v
  by_cases hv : v = w
  · subst hv
    rw [Function.update_self, Function.update_self, glEquivOfRingEquiv_apply_entry, circleGL2_apply]
    simp
  · rw [Function.update_of_ne hv, Function.update_of_ne hv]
    simp

theorem borelDiagSnd_archCircleAt (hw : w.IsComplex) (ζ : ℂˣ) :
    borelDiagSnd ⟨archCircleAt hw ζ, archCircleAt_mem_adelicBorel hw ζ⟩ =
      archUnitHom w (Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ⁻¹) := by
  apply Units.ext
  show ((archCircleAt hw ζ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
    ((Function.update (1 : Π v : InfinitePlace K, v.Completion) w
      ((Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ⁻¹ : (w.Completion)ˣ) : w.Completion), 1) :
        AdeleRing (𝓞 K) K)
  rw [archCircleAt_eq, adelicArchGLInclAt_apply]
  refine Prod.ext (funext fun v => ?_) (by simp)
  show Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
      ((glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (circleGL2 ζ) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) v 1 1 =
    Function.update (1 : Π v : InfinitePlace K, v.Completion) w
      ((Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ⁻¹ : (w.Completion)ˣ) : w.Completion) v
  by_cases hv : v = w
  · subst hv
    rw [Function.update_self, Function.update_self, glEquivOfRingEquiv_apply_entry, circleGL2_apply]
    simp
  · rw [Function.update_of_ne hv, Function.update_of_ne hv]
    simp

theorem glFin_archCircleAt (hw : w.IsComplex) (ζ : ℂˣ) : glFin (𝓞 K) K (archCircleAt hw ζ) = 1 :=
  glFin_adelicArchGLIncl K _

theorem archComponent_glArch_archCircleAt_of_ne (hw : w.IsComplex) (ζ : ℂˣ) {v : InfinitePlace K} (hvw : v ≠ w) :
    archComponent K v (glArch (𝓞 K) K (archCircleAt hw ζ)) = 1 :=
  archComponent_glArch_adelicArchGLInclAt_of_ne hvw _

theorem adelicArchGLInclAt_mem_adelicBorel (a : GL (Fin 2) w.Completion)
    (ha : (a : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) :
    adelicArchGLInclAt K w a ∈ adelicBorel (𝓞 K) K := by
  rw [adelicBorel, mem_borelSubgroup_iff, adelicArchGLInclAt_apply]
  refine Prod.ext (funext fun v => ?_) ?_
  · show Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        (a : Matrix (Fin 2) (Fin 2) w.Completion) v 1 0 = 0
    by_cases hv : v = w
    · subst hv
      rw [Function.update_self, ha]
    · rw [Function.update_of_ne hv]
      simp
  · show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0 = 0
    simp

def diagGL {A : Type*} [CommRing A] (δ : Aˣ) : GL (Fin 2) A where
  val := !![(δ : A), 0; 0, 1]
  inv := !![((δ⁻¹ : Aˣ) : A), 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagGL_coe {A : Type*} [CommRing A] (δ : Aˣ) :
    (diagGL δ : Matrix (Fin 2) (Fin 2) A) = !![(δ : A), 0; 0, 1] := rfl

theorem diagGL_inv_coe {A : Type*} [CommRing A] (δ : Aˣ) :
    (((diagGL δ)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((δ⁻¹ : Aˣ) : A), 0; 0, 1] := rfl

theorem diag_mem_adelicBorel (δ : (w.Completion)ˣ) : adelicArchGLInclAt K w (diagGL δ) ∈ adelicBorel (𝓞 K) K :=
  adelicArchGLInclAt_mem_adelicBorel _ (by simp [diagGL_coe])

theorem borelDiagFst_diag (δ : (w.Completion)ˣ) :
    borelDiagFst ⟨adelicArchGLInclAt K w (diagGL δ), diag_mem_adelicBorel δ⟩ = archUnitHom w δ := by
  apply Units.ext
  show ((adelicArchGLInclAt K w (diagGL δ) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
    ((Function.update (1 : Π v : InfinitePlace K, v.Completion) w (δ : w.Completion), 1) : AdeleRing (𝓞 K) K)
  rw [adelicArchGLInclAt_apply]
  refine Prod.ext (funext fun v => ?_) (by simp)
  show Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
      (diagGL δ : Matrix (Fin 2) (Fin 2) w.Completion) v 0 0 =
    Function.update (1 : Π v : InfinitePlace K, v.Completion) w (δ : w.Completion) v
  by_cases hv : v = w
  · subst hv
    rw [Function.update_self, Function.update_self, diagGL_coe]
    simp
  · rw [Function.update_of_ne hv, Function.update_of_ne hv]
    simp

theorem borelDiagSnd_diag (δ : (w.Completion)ˣ) :
    borelDiagSnd ⟨adelicArchGLInclAt K w (diagGL δ), diag_mem_adelicBorel δ⟩ = 1 := by
  apply Units.ext
  show ((adelicArchGLInclAt K w (diagGL δ) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
    (1 : AdeleRing (𝓞 K) K)
  rw [adelicArchGLInclAt_apply]
  refine Prod.ext (funext fun v => ?_) (by show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1 = 1; simp)
  show Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
      (diagGL δ : Matrix (Fin 2) (Fin 2) w.Completion) v 1 1 = 1
  by_cases hv : v = w
  · subst hv
    rw [Function.update_self, diagGL_coe]
    simp
  · rw [Function.update_of_ne hv]
    simp

theorem exists_diag_mul_detOne (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k) :
    ∃ (δ : (w.Completion)ˣ) (k₁ : rowIsometrySubgroup₀ w.Completion),
      k = diagGL δ * (k₁ : GL (Fin 2) w.Completion) := by
  have hdet1 : ‖(k : Matrix (Fin 2) (Fin 2) w.Completion).det‖ = 1 := hk.1
  have hdet0 : (k : Matrix (Fin 2) (Fin 2) w.Completion).det ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet1; exact zero_ne_one hdet1
  set δ : (w.Completion)ˣ := Units.mk0 _ hdet0 with hδ
  have hδv : (δ : w.Completion) = (k : Matrix (Fin 2) (Fin 2) w.Completion).det := rfl
  have hδn : ‖(δ : w.Completion)‖ = 1 := by rw [hδv]; exact hdet1
  have hδin : ‖((δ⁻¹ : (w.Completion)ˣ) : w.Completion)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hδn, inv_one]
  set k₁ : GL (Fin 2) w.Completion := (diagGL δ)⁻¹ * k with hk₁

  have e00 : (k₁ : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = ((δ⁻¹ : (w.Completion)ˣ) : w.Completion) * (k : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 := by
    rw [hk₁, Units.val_mul, diagGL_inv_coe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (k₁ : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = ((δ⁻¹ : (w.Completion)ˣ) : w.Completion) * (k : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 := by
    rw [hk₁, Units.val_mul, diagGL_inv_coe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (k₁ : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 := by
    rw [hk₁, Units.val_mul, diagGL_inv_coe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (k₁ : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 := by
    rw [hk₁, Units.val_mul, diagGL_inv_coe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdetk₁ : (k₁ : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
    rw [hk₁, Units.val_mul, Matrix.det_mul, diagGL_inv_coe, Matrix.det_fin_two_of, ← hδv]
    simp
  refine ⟨δ, ⟨k₁, ?_⟩, ?_⟩
  · rw [mem_rowIsometrySubgroup₀_iff]
    refine ⟨hdetk₁, ?_, fun x y => ?_⟩
    · rw [hdetk₁, norm_one]
    · rw [e00, e01, e10, e11]
      have h := hk.2 (x * ((δ⁻¹ : (w.Completion)ˣ) : w.Completion)) y
      rw [norm_mul, hδin, mul_one] at h
      simpa only [mul_assoc] using h
  · show k = diagGL δ * ((diagGL δ)⁻¹ * k)
    rw [mul_inv_cancel_left]

theorem archUnitHom_coe (u : (w.Completion)ˣ) :
    ((archUnitHom w u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      (Function.update (1 : Π v : InfinitePlace K, v.Completion) w (u : w.Completion), 1) := rfl

theorem ideleNorm_archUnitHom (u : (w.Completion)ˣ) :
    NumberField.TateGlobal.ideleNorm K (archUnitHom w u) = ‖(u : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w u) rfl,
    archUnitHom_coe]
  rw [Finset.prod_eq_single w]
  · simp
  · intro v _ hv
    simp [Function.update_of_ne hv]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem ideleNorm_archUnitHom_of_norm_eq_one (u : (w.Completion)ˣ) (hu : ‖(u : w.Completion)‖ = 1) :
    NumberField.TateGlobal.ideleNorm K (archUnitHom w u) = 1 := by
  rw [ideleNorm_archUnitHom, hu, one_pow]

theorem norm_ringEquivComplexOfIsComplex_symm (hw : w.IsComplex) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
  rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) ((ringEquivComplexOfIsComplex hw).symm z),
    extensionEmbedding_symm]

theorem ideleNorm_archUnitHom_circle (hw : w.IsComplex) (ζ : ℂˣ) (hζ : ‖(ζ : ℂ)‖ = 1) :
    NumberField.TateGlobal.ideleNorm K
      (archUnitHom w (Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) ζ)) = 1 := by
  apply ideleNorm_archUnitHom_of_norm_eq_one
  show ‖(ringEquivComplexOfIsComplex hw).symm (ζ : ℂ)‖ = 1
  rw [norm_ringEquivComplexOfIsComplex_symm, hζ]

end WBPlumb

namespace WB

variable {K : Type} [Field K] [NumberField K]

theorem zpow_exponent_unique {w : InfinitePlace K} (hw : w.IsComplex) {a b : ℤ}
    (h : ∀ u : (w.Completion)ˣ, ‖extensionEmbedding w (u : w.Completion)‖ = 1 →
      (extensionEmbedding w (u : w.Completion)) ^ a = (extensionEmbedding w (u : w.Completion)) ^ b) : a = b := by
  by_contra hne
  have hd : ((a - b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := ((a - b : ℤ) : ℝ)⁻¹ with hθ
  set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζ
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ1 : ‖ζ‖ = 1 := by simp [hζ, Complex.norm_exp_ofReal_mul_I]
  set u : (w.Completion)ˣ := Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →* w.Completion) (Units.mk0 ζ hζ0) with hu
  have heu : extensionEmbedding w (u : w.Completion) = ζ := WBPlumb.extensionEmbedding_symm hw ζ
  have h1 := h u (by rw [heu, hζ1])
  rw [heu] at h1
  have h2 : ζ ^ (a - b) = 1 := by rw [zpow_sub₀ hζ0, h1, div_self (zpow_ne_zero _ hζ0)]
  rw [hζ, ← Complex.exp_int_mul] at h2
  have h3 : ((a - b : ℤ) : ℂ) * ((θ : ℂ) * Complex.I) = Complex.I := by
    have : ((a - b : ℤ) : ℝ) * θ = 1 := mul_inv_cancel₀ hd
    have h4 : (((a - b : ℤ) : ℝ) : ℂ) * ((θ : ℝ) : ℂ) = 1 := by exact_mod_cast this
    push_cast at h4 ⊢
    linear_combination Complex.I * h4
  rw [h3] at h2

  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have him := congrArg Complex.im hn
  simp only [Complex.I_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero,
    add_zero, mul_one] at him
  have hpos : (0 : ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
  have hn1 : (1 : ℤ) ≤ n := by have := Int.cast_pos.1 hpos; omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  nlinarith [Real.pi_gt_three]

end WB

open WB WBPlumb NumberField.InfinitePlace.Completion NumberField.TateGlobal in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ M₀ : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) φ)
      (_hφK : IsArchKFinite K φ) (_hφf : IsKfSmooth K φ) (_hφc : Continuous φ)
      (_hφKu : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
          (fun k : ↥(archRowIsometrySubgroup K w) => φ (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
      (_hφty : φ ∈ archCutSubmodule K tysK)
      (_hφ0 : φ ≠ 0)
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (_hreal : ∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1)),
      ∀ v : InfinitePlace K, |mμ v| ≤ (M₀ : ℤ) ∧ |mν v| ≤ (M₀ : ℤ) := by
  intro αm
  classical
  obtain ⟨n₀, hWP⟩ := AutomorphicForm.exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt K tysK

  let P : InfinitePlace K → ℤ → Prop := fun v m => ∀ u : (v.Completion)ˣ,
    ‖extensionEmbedding v (u : v.Completion)‖ = 1 →
      ((ξK ⟨archUnitHom v u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = (extensionEmbedding v (u : v.Completion)) ^ m
  let mξ : InfinitePlace K → ℤ := fun v => if h : ∃ m, P v m then h.choose else 0
  refine ⟨n₀ + Finset.univ.sup (fun v => (mξ v).natAbs) + 1, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν φ hφ hφK hφf hφc hφKu hφlev hφty hφ0 mμ mν hmμ hmν hreal v
  have hsup : ((mξ v).natAbs : ℤ) ≤ ((Finset.univ.sup fun v => (mξ v).natAbs : ℕ) : ℤ) := by
    exact_mod_cast Finset.le_sup (f := fun v => (mξ v).natAbs) (Finset.mem_univ v)
  by_cases hvr : v.IsReal
  · obtain ⟨h1, h2⟩ := hreal v hvr
    constructor
    · rcases h1 with h | h <;> (rw [h]; simp only [abs_zero, abs_one]; push_cast; omega)
    · rcases h2 with h | h <;> (rw [h]; simp only [abs_zero, abs_one]; push_cast; omega)
  have hv : v.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hvr

  have hunit : ∀ u : (v.Completion)ˣ, ‖extensionEmbedding v (u : v.Completion)‖ = 1 →
      NumberField.TateGlobal.ideleNorm K (archUnitHom v u) = 1 := fun u hu =>
    ideleNorm_archUnitHom_of_norm_eq_one u (by
      rwa [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)] at hu)
  have hPsum : P v (mμ v + mν v) := by
    intro u hu
    have e := hμν (archUnitHom v u)
    rw [hunit u hu, Real.one_rpow, Complex.ofReal_one, mul_one] at e
    rw [← e, show μ (archUnitHom v u) = NumberField.TateGlobal.archLocalChar μ v u from rfl,
      show ν (archUnitHom v u) = NumberField.TateGlobal.archLocalChar ν v u from rfl, hmμ v u hu, hmν v u hu,
      ← zpow_add₀ (norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero))]
  have hmξ : mξ v = mμ v + mν v := by
    have hex : ∃ m, P v m := ⟨_, hPsum⟩
    have hch : P v (mξ v) := by
      show P v (if h : ∃ m, P v m then h.choose else 0)
      rw [dif_pos hex]
      exact hex.choose_spec
    exact zpow_exponent_unique hv fun u hu => by rw [← hch u hu, ← hPsum u hu]

  have hdiff : |mμ v - mν v| ≤ (n₀ : ℤ) := by

    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ0 (funext h)
    obtain ⟨b, k, hb, -, hk, hxk⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K x
    have hφk : φ k ≠ 0 := by
      intro h0
      apply hx
      rw [hxk, hφ b hb k, h0, mul_zero]

    set kv : GL (Fin 2) v.Completion := archComponent K v (glArch (𝓞 K) K k) with hkv
    obtain ⟨δ, k₁, hkd⟩ := exists_diag_mul_detOne kv (hk v)
    set h : AdelicGL2 (𝓞 K) K := (adelicArchGLInclAt K v kv)⁻¹ * k with hh
    have hh1 : archComponent K v (glArch (𝓞 K) K h) = 1 := archComponent_glArch_inv_incl_mul k
    have hk_eq : k = adelicArchGLInclAt K v (diagGL δ) * (rowIsometryInclAt₀ K v k₁ * h) := by
      rw [rowIsometryInclAt₀_apply, ← mul_assoc, ← map_mul, ← hkd, hh, mul_inv_cancel_left]
    have hφ1 : φ (rowIsometryInclAt₀ K v k₁ * h) ≠ 0 := by
      intro h0
      apply hφk
      rw [hk_eq, hφ _ (diag_mem_adelicBorel δ), h0, mul_zero]

    set f : AdelicGL2 (𝓞 K) K → ℂ := fun y => φ (y * rowIsometryInclAt₀ K v k₁) with hf
    have hfc : Continuous f := hφc.comp (continuous_mul_right _)
    have hft : f ∈ ⨆ i : Fin (tysK.card v), archTypeSubmoduleAt K v (tysK.rep v i) :=
      (mem_archCutSubmodule_iff K tysK f).1 (comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule K hφty v k₁) v
    have hfh : f h ≠ 0 := by
      show φ (h * rowIsometryInclAt₀ K v k₁) ≠ 0
      rwa [rowIsometryInclAt₀_apply, ← mul_comm_of_archComponent_eq_one _ hh1, ← rowIsometryInclAt₀_apply]

    have hlaw : ∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (h * archCircleAt hv ζ) = (ζ : ℂ) ^ (mμ v - mν v) * f h := by
      intro ζ hζ
      show φ (h * archCircleAt hv ζ * rowIsometryInclAt₀ K v k₁) = (ζ : ℂ) ^ (mμ v - mν v) * φ (h * rowIsometryInclAt₀ K v k₁)
      have hcomm : h * archCircleAt hv ζ = archCircleAt hv ζ * h :=
        (mul_comm_of_archComponent_eq_one _ hh1).symm
      rw [hcomm, mul_assoc, hφ _ (archCircleAt_mem_adelicBorel hv ζ), borelDiagFst_archCircleAt, borelDiagSnd_archCircleAt]
      set u : (v.Completion)ˣ := Units.map ((ringEquivComplexOfIsComplex hv).symm : ℂ →* v.Completion) ζ with hu
      set u' : (v.Completion)ˣ := Units.map ((ringEquivComplexOfIsComplex hv).symm : ℂ →* v.Completion) ζ⁻¹ with hu'
      have heu : extensionEmbedding v (u : v.Completion) = (ζ : ℂ) := extensionEmbedding_symm hv _
      have heu' : extensionEmbedding v (u' : v.Completion) = ((ζ⁻¹ : ℂˣ) : ℂ) := extensionEmbedding_symm hv _
      have hnu : ‖extensionEmbedding v (u : v.Completion)‖ = 1 := by rw [heu, hζ]
      have hnu' : ‖extensionEmbedding v (u' : v.Completion)‖ = 1 := by
        rw [heu', Units.val_inv_eq_inv_val, norm_inv, hζ, inv_one]
      have e1 : ((etaFst μ αm hαm 0 (archUnitHom v u) : ℂˣ) : ℂ) = (ζ : ℂ) ^ (mμ v) := by
        rw [etaFst_apply, Units.val_mul, show μ (archUnitHom v u) = NumberField.TateGlobal.archLocalChar μ v u from rfl,
          hmμ v u hnu, heu]
        have : ((cpowChar αm hαm (0 + 1 / 2) (archUnitHom v u) : ℂˣ) : ℂ) = 1 := by
          show ((((αm (archUnitHom v u) : ℝˣ) : ℝ) : ℂ)) ^ ((0 : ℂ) + 1 / 2) = 1
          have : ((αm (archUnitHom v u) : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K (archUnitHom v u) := rfl
          rw [this, hunit u hnu, Complex.ofReal_one, Complex.one_cpow]
        rw [this, mul_one]
      have e2 : ((etaSnd ν αm hαm 0 (archUnitHom v u') : ℂˣ) : ℂ) = ((ζ⁻¹ : ℂˣ) : ℂ) ^ (mν v) := by
        rw [etaSnd_apply, Units.val_mul, show ν (archUnitHom v u') = NumberField.TateGlobal.archLocalChar ν v u' from rfl,
          hmν v u' hnu', heu']
        have : ((cpowChar αm hαm (-(0 + 1 / 2)) (archUnitHom v u') : ℂˣ) : ℂ) = 1 := by
          show ((((αm (archUnitHom v u') : ℝˣ) : ℝ) : ℂ)) ^ (-((0 : ℂ) + 1 / 2)) = 1
          have : ((αm (archUnitHom v u') : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K (archUnitHom v u') := rfl
          rw [this, hunit u' hnu', Complex.ofReal_one, Complex.one_cpow]
        rw [this, mul_one]
      rw [e1, e2, Units.val_inv_eq_inv_val, inv_zpow', ← zpow_add₀ (ζ.ne_zero), ← sub_eq_add_neg]
    exact hWP v hv f hfc hft h (mμ v - mν v) hlaw hfh

  have hA := abs_le.1 hdiff
  have hξb : |mξ v| ≤ ((Finset.univ.sup fun v => (mξ v).natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]; exact hsup
  have hB := abs_le.1 hξb
  rw [hmξ] at hB
  constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> omega

end

end S_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule (solution)
