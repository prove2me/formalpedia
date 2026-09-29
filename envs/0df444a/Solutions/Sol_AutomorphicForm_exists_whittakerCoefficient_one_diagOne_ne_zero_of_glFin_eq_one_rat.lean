-- Prove2me | solution 1 for AutomorphicForm.exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d9fe80c4-97a2-533d-ac21-d204212c5875

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicVolume
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AdelicDock

namespace P2M
namespace ArchTorusC9

abbrev w₀ : InfinitePlace ℚ := Rat.infinitePlace
theorem hw₀ : InfinitePlace.IsReal w₀ := Rat.isReal_infinitePlace

section Generic

variable {F : Type} [Field F] [NumberField F]

theorem eq_of_parts_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem eq_archPart_mul_finPart (g : AdelicGL2 (𝓞 F) F) :
    g = adelicArchGLIncl F (glArch (𝓞 F) F g) * finEmbed (𝓞 F) F (glFin (𝓞 F) F g) := by
  refine eq_of_parts_eq ?_ ?_
  · rw [map_mul, glArch_adelicArchGLIncl, glArch_finEmbed, mul_one]
  · rw [map_mul, glFin_adelicArchGLIncl, glFin_finEmbed, one_mul]

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

theorem coe_archComponent (w : InfinitePlace F) (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((archComponent F w k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = (archEval F w).mapMatrix (k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  ext i j
  rw [archComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, archEval_apply]

theorem coe_glEquivOfRingEquiv {K L : Type*} [NormedField K] [NormedField L] (e : K ≃+* L) (k : GL (Fin 2) K) :
    ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = e.toRingHom.mapMatrix (k : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; rfl

theorem W_translate (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (α : F) (g h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * h) = whittakerCoefficient F pins ψ (fun y => φ (y * h)) α g := by
  simp only [whittakerCoefficient, mul_assoc]

theorem W_const_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (a : ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun y => a * φ y) α g = a * whittakerCoefficient F pins ψ φ α g := by
  simp only [whittakerCoefficient, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem W_mul_right_of_forall (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : AdelicGL2 (𝓞 F) F) (c : ℂ) (hk : ∀ y, φ (y * k) = c * φ y)
    (α : F) (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (h * k) = c * whittakerCoefficient F pins ψ φ α h := by
  rw [W_translate, show (fun y => φ (y * k)) = fun y => c * φ y from funext hk, W_const_mul]

theorem W_centralScalar_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (z : (AdeleRing (𝓞 F) F)ˣ) (c : ℂ)
    (hz : ∀ y, φ (centralScalar (𝓞 F) F z * y) = c * φ y) (α : F) (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (centralScalar (𝓞 F) F z * h) = c * whittakerCoefficient F pins ψ φ α h := by
  rw [← mul_centralScalar_comm]
  exact W_mul_right_of_forall pins ψ φ _ c (fun y => by rw [mul_centralScalar_comm, hz]) α h

theorem adelicArchGLInclAt_scalar_eq_centralScalar {w : InfinitePlace F} (hw : w.IsReal) (t : ℝˣ) :
    adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t))
      = centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) := by
  apply eq_of_parts_eq
  · show glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) = _
    rw [glArch_adelicArchGLIncl]
    apply Units.ext
    apply Matrix.ext
    intro i j
    funext v
    show archMatrixUpdate F w _ i j v = _
    rw [show ((glArch (𝓞 F) F (centralScalar (𝓞 F) F
        (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t))) :
          GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j v
        = (((centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 v from rfl,
      centralScalar_val]
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
          archCentralUnit_fst_self]
      all_goals rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, archCentralUnit_fst_of_ne _ _ hv]
      all_goals rfl
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) = _
    rw [glFin_adelicArchGLIncl]
    apply Units.ext
    apply Matrix.ext
    intro i j
    show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = (((centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
    rw [centralScalar_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, archCentralUnit_snd]
    all_goals rfl

end Generic

section RatArch

theorem glArch_ext_rat {k k' : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ Rat.infinitePlace k = archComponent ℚ Rat.infinitePlace k') : k = k' := by
  apply Units.ext
  ext i j
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  have := congrArg (fun m : GL (Fin 2) Rat.infinitePlace.Completion =>
    (m : Matrix (Fin 2) (Fin 2) Rat.infinitePlace.Completion) i j) h
  simpa only [archComponent_apply] using this

def realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw₀).toRingHom
    (archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g))

theorem glEquiv_symm_realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw₀).symm (realGL g) =
      archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) := by
  apply Units.ext
  ext i j : 1
  show (ringEquivRealOfIsReal hw₀).symm ((ringEquivRealOfIsReal hw₀).toRingHom
    ((archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) : Matrix (Fin 2) (Fin 2) _) i j)) = _
  exact (ringEquivRealOfIsReal hw₀).symm_apply_apply _

theorem archRealGLAt_eq_adelicArchGLInclAt (m : GL (Fin 2) ℝ) :
    archRealGLAt hw₀ m = adelicArchGLInclAt ℚ w₀ (glEquivOfRingEquiv (ringEquivRealOfIsReal hw₀).symm m) := rfl

theorem archComponent_glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    archComponent ℚ w₀ (glArch (𝓞 ℚ) ℚ (archRealGLAt hw₀ m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw₀).symm m := by
  rw [archRealGLAt_eq_adelicArchGLInclAt]
  unfold adelicArchGLInclAt
  rw [MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archRealGLAt_realGL_eq (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt hw₀ (realGL g) = adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ g) := by
  apply eq_of_parts_eq
  · rw [glArch_adelicArchGLIncl]
    apply glArch_ext_rat
    rw [archComponent_glArch_archRealGLAt, glEquiv_symm_realGL]
  · rw [glFin_adelicArchGLIncl, archRealGLAt_eq_adelicArchGLInclAt]
    unfold adelicArchGLInclAt
    rw [MonoidHom.comp_apply, glFin_adelicArchGLIncl]

theorem eq_archRealGLAt_realGL_of_glFin_eq_one (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : glFin (𝓞 ℚ) ℚ g = 1) :
    g = archRealGLAt hw₀ (realGL g) := by
  rw [archRealGLAt_realGL_eq]
  conv_lhs => rw [eq_archPart_mul_finPart g]
  rw [hg, map_one, mul_one]

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt hw₀ m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem archRealLiftAt_coe (m : GL (Fin 2) ℝ) :
    archRealLiftAt hw₀ (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) = archRealGLAt hw₀ m := by
  have hdet : (Matrix.of (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]; exact Matrix.GeneralLinearGroup.det_ne_zero m
  rw [archRealLiftAt_of_det_ne_zero hw₀ hdet]
  congr 1
  apply Units.ext
  simp only [Equiv.apply_symm_apply]
  rfl

theorem archRealGLAt_unipotentGL2 (t : ℝ) :
    archRealGLAt hw₀ (unipotentGL2 t) =
      unipotentGL2 (((archRealGLAt hw₀ (unipotentGL2 t) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1) := by
  have hfin : glFin (𝓞 ℚ) ℚ (archRealGLAt hw₀ (unipotentGL2 t)) = 1 := glFin_archRealGLAt _
  have harch := archComponent_glArch_archRealGLAt (unipotentGL2 t)
  have h01a : (((archRealGLAt hw₀ (unipotentGL2 t) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1).1 w₀ = (ringEquivRealOfIsReal hw₀).symm t := by
    have : (((archRealGLAt hw₀ (unipotentGL2 t) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1).1 w₀
        = ((archComponent ℚ w₀ (glArch (𝓞 ℚ) ℚ (archRealGLAt hw₀ (unipotentGL2 t))) : GL (Fin 2) _) :
            Matrix (Fin 2) (Fin 2) _) 0 1 := rfl
    rw [this, harch, glEquivOfRingEquiv_apply_entry, unipotentGL2_coe]
    simp
  have h01f : (((archRealGLAt hw₀ (unipotentGL2 t) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1).2 = 0 := by
    have : (((archRealGLAt hw₀ (unipotentGL2 t) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1).2
        = ((glFin (𝓞 ℚ) ℚ (archRealGLAt hw₀ (unipotentGL2 t)) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 0 1 := rfl
    rw [this, hfin, Units.val_one, Matrix.one_apply_ne (by decide)]
  refine eq_of_parts_eq ?_ ?_
  · apply glArch_ext_rat
    rw [harch]
    apply Units.ext
    rw [coe_glEquivOfRingEquiv, mapMatrix_unipotentGL2, coe_archComponent, coe_glArch, mapMatrix_unipotentGL2,
      mapMatrix_unipotentGL2, archEval_apply, adeleArch_apply, h01a]
    rfl
  · rw [hfin]
    apply Units.ext
    rw [coe_glFin, mapMatrix_unipotentGL2, adeleFin_apply, h01f, unipotentGL2_zero]

theorem archRealGLAt_diagOne (r : ℝˣ) :
    archRealGLAt hw₀ (diagOne r) =
      diagOne (archCentralUnit ℚ w₀ (Units.map (ringEquivRealOfIsReal hw₀).symm.toRingHom.toMonoidHom r)) := by
  refine eq_of_parts_eq ?_ ?_
  · apply glArch_ext_rat
    rw [archComponent_glArch_archRealGLAt]
    apply Units.ext
    ext i j
    rw [glEquivOfRingEquiv_apply_entry, diagOne_coe_apply, archComponent_apply, glArch_apply, diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, archCentralUnit_fst_self]
    all_goals rfl
  · rw [glFin_archRealGLAt]
    apply Units.ext
    ext i j
    rw [glFin_apply, diagOne_coe_apply, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, archCentralUnit_snd]
    all_goals rfl

theorem archRealGLAt_scalar (t : ℝˣ) :
    archRealGLAt hw₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) t) =
      centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w₀ (Units.map (ringEquivRealOfIsReal hw₀).symm.toRingHom.toMonoidHom t)) := by
  rw [← adelicArchGLInclAt_scalar_eq_centralScalar hw₀ t, archRealGLAt_eq_adelicArchGLInclAt]
  rfl

end RatArch

end P2M.ArchTorusC9

p2m_open "IsDedekindDomain NumberField NumberField.InfinitePlace.NumberField MeasureTheory Matrix"
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicVolume
p2m_open "NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AdelicDock P2M.ArchTorusC9 in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) * g) = φ (unipotentGL2 u * g))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ)
    (hcent : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = χ z * φ g)
    (n : ℤ) (hwt : HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightCharAt Rat.isReal_infinitePlace n) φ)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) (hx : glFin (𝓞 ℚ) ℚ x = 1)
    (hW : whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 x ≠ 0) :
    ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
      whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 (diagOne a) ≠ 0 := by
  classical
  have hPI : IsPrincipalInvariantAddChar ℚ NumberField.StandardAddChar.psiQ :=
    NumberField.StandardAddChar.isGlobalAddChar_psiQ.principalInvariant
  set e := ringEquivRealOfIsReal hw₀ with hedef
  have he' : ∀ s : ℝ, ‖e.symm s‖ = ‖s‖ := fun s => by
    conv_rhs => rw [← e.apply_symm_apply s]
    exact (norm_ringEquivRealOfIsReal hw₀ _).symm
  have hmem : ∀ r : rowIsometrySubgroup₀ ℝ, glEquivOfRingEquiv e.symm (r : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w₀.Completion :=
    fun r => map_mem_rowIsometrySubgroup₀_of_normPreserving e.symm he' r r.2

  set B : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun y =>
    whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1
      (archRealLiftAt hw₀ (Matrix.of.symm y)) with hB

  set uf : ℝ → ℂ := fun t => NumberField.StandardAddChar.psiQ
    ((((archRealGLAt hw₀ (unipotentGL2 t) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1)) with huf
  set zf : ℝ → ℂ := fun t => if h : t = 0 then 0 else
    χ (archCentralUnit ℚ w₀ (Units.map e.symm.toRingHom.toMonoidHom (Units.mk0 t h))) with hzf
  set kf : rowIsometrySubgroup₀ ℝ → ℂ := fun r =>
    ((archWeightCharAt hw₀ n ⟨glEquivOfRingEquiv e.symm (r : GL (Fin 2) ℝ), hmem r⟩ : ℂˣ) : ℂ) with hkf

  have hU : ∀ (t : ℝ) (y : Matrix (Fin 2) (Fin 2) ℝ), y.det ≠ 0 → B (!![1, t; 0, 1] * y) = uf t * B y := by
    intro t y hy
    have hy' : (Matrix.of (Matrix.of.symm y)).det ≠ 0 := by rwa [Equiv.apply_symm_apply]
    have hty : (Matrix.of (Matrix.of.symm (!![1, t; 0, 1] * y))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_fin_two_of]; simpa using hy
    simp only [hB, huf]
    rw [archRealLiftAt_of_det_ne_zero hw₀ hty, archRealLiftAt_of_det_ne_zero hw₀ hy']
    have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hty
        = unipotentGL2 t * Matrix.GeneralLinearGroup.mkOfDetNeZero _ hy' := by
      apply Units.ext
      show Matrix.of (Matrix.of.symm (!![1, t; 0, 1] * y))
        = ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of (Matrix.of.symm y)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, unipotentGL2_coe]
    rw [hmk, map_mul, archRealGLAt_unipotentGL2,
      AutomorphicForm.whittakerCoefficient_unipotentGL2_mul ℚ D U gen NumberField.StandardAddChar.psiQ hPI φ _
        (fun β u => hper β u _) 1 _, map_one, one_mul]
    congr 2

  have hZ : ∀ (t : ℝ) (y : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → y.det ≠ 0 → B (t • y) = zf t * B y := by
    intro t y ht hy
    have hy' : (Matrix.of (Matrix.of.symm y)).det ≠ 0 := by rwa [Equiv.apply_symm_apply]
    have hty : (Matrix.of (Matrix.of.symm (t • y))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ ht.ne') hy
    simp only [hB, hzf, dif_neg ht.ne']
    rw [archRealLiftAt_of_det_ne_zero hw₀ hty, archRealLiftAt_of_det_ne_zero hw₀ hy']
    have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hty
        = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht.ne') * Matrix.GeneralLinearGroup.mkOfDetNeZero _ hy' := by
      apply Units.ext
      show Matrix.of (Matrix.of.symm (t • y)) = Matrix.scalar (Fin 2) t * Matrix.of (Matrix.of.symm y)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rw [hmk, map_mul, archRealGLAt_scalar]
    exact W_centralScalar_mul _ _ φ _ _ (fun g => hcent _ g) 1 _

  have hK : ∀ (r : rowIsometrySubgroup₀ ℝ) (xm : GL (Fin 2) ℝ),
      B ((xm * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = kf r * B (xm : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro r xm
    simp only [hB, hkf]
    rw [archRealLiftAt_coe, archRealLiftAt_coe, map_mul]
    exact W_mul_right_of_forall _ _ φ _ _ (fun g => hwt ⟨glEquivOfRingEquiv e.symm (r : GL (Fin 2) ℝ), hmem r⟩ g) 1 _

  have hBx : B ((realGL x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
    simp only [hB]
    rw [archRealLiftAt_coe, ← eq_archRealGLAt_realGL_of_glFin_eq_one x hx]
    exact hW
  have hdet : ((realGL x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero _

  obtain ⟨ε, hε, hxε⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < ε * ((realGL x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rcases lt_or_gt_of_ne hdet with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩

  obtain ⟨y, hy, hBy⟩ : ∃ y : ℝ, 0 < y ∧ B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hBx (AutomorphicForm.eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos B uf zf kf hU hZ hK ε hε
      (fun y hy => hcon y hy) _ hxε)

  have hs0 : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have hεy : ε * y ≠ 0 := by
    rcases hε with rfl | rfl
    · simpa using hy.ne'
    · simpa using hy.ne'
  have hray : !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = (Real.sqrt y)⁻¹ • !![ε * y, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j
    · show ε * Real.sqrt y = (Real.sqrt y)⁻¹ * (ε * y)
      field_simp
      linear_combination ε * hs
    · simp
    · simp
    · simp
  have hdetD : (!![ε * y, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simpa using hεy
  have hBD : B !![ε * y, 0; 0, 1] ≠ 0 := by
    intro h0
    apply hBy
    rw [hray, hZ _ _ (inv_pos.mpr (Real.sqrt_pos.mpr hy)) hdetD, h0, mul_zero]

  set r : ℝˣ := Units.mk0 (ε * y) hεy with hr
  have hD : (!![ε * y, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = ((diagOne r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    rw [diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hr]
  refine ⟨archCentralUnit ℚ w₀ (Units.map (ringEquivRealOfIsReal hw₀).symm.toRingHom.toMonoidHom r),
    archCentralUnit_snd w₀ _, ?_⟩
  rw [← archRealGLAt_diagOne, ← archRealLiftAt_coe, ← hD]
  exact hBD

end

end S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat (solution)
