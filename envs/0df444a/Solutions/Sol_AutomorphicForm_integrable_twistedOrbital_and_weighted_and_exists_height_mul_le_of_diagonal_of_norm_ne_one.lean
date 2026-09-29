-- Prove2me | solution 1 for AutomorphicForm.integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ca98779e-f90b-5375-94e1-31528979f287

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.TateGlobal AutomorphicForm
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace R1S80OrbInt

section Height

variable (L : Type) [Field L] [NumberField L]

theorem adelicHeight_borel_mul {b : AdelicGL2 (𝓞 L) L} (hb : b ∈ adelicBorel (𝓞 L) L) (g : AdelicGL2 (𝓞 L) L) :
    adelicHeight L (b * g)
      = ideleNorm L (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)))
        * (ideleNorm L (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))))⁻¹
        * adelicHeight L g := by
  obtain ⟨hpos, -, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow L
  have h := hind hpos (1 / 2) b hb g
  simp only at h
  have hexp : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  rw [etaFst_apply, etaSnd_apply] at h
  simp only [MonoidHom.one_apply, one_mul, cpowChar_apply_val,
    MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, NNReal.coe_toRealHom] at h
  rw [hexp, Complex.cpow_one, Complex.cpow_one, Complex.cpow_one, Complex.cpow_neg_one] at h
  have h' : adelicHeight L (b * g)
      = ((distribHaarChar (AdeleRing (𝓞 L) L)
            (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) : ℝ≥0) : ℝ)
        * (((distribHaarChar (AdeleRing (𝓞 L) L)
            (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) : ℝ≥0) : ℝ))⁻¹
        * adelicHeight L g := by
    exact_mod_cast h
  exact h'

theorem val_mul_apply' (x y : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((x * y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 0 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 1 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem adelicWeyl_val :
    ((adelicWeyl (𝓞 L) L : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = !![0, 1; 1, 0] := by
  ext i j
  show algebraMap L (AdeleRing (𝓞 L) L) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) L) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_inv : (adelicWeyl (𝓞 L) L)⁻¹ = adelicWeyl (𝓞 L) L := by
  unfold adelicWeyl
  rw [← map_inv, gl2Weyl_inv]

theorem weyl_conj_diag (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    ((adelicWeyl (𝓞 L) L * h * (adelicWeyl (𝓞 L) L)⁻¹ : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![(h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1, 0; 0, (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0] := by
  rw [adelicWeyl_inv]
  ext i j
  simp only [val_mul_apply', adelicWeyl_val, h10, h01]
  fin_cases i <;> fin_cases j <;> simp

theorem height_prod_diag_mul (h y : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    adelicHeight L (h * y) * adelicHeight L (adelicWeyl (𝓞 L) L * (h * y)) =
      adelicHeight L y * adelicHeight L (adelicWeyl (𝓞 L) L * y) := by
  set w := adelicWeyl (𝓞 L) L with hw
  have hb : h ∈ adelicBorel (𝓞 L) L := h10
  set h' : AdelicGL2 (𝓞 L) L := w * h * w⁻¹ with hh'
  have hval := weyl_conj_diag L h h10 h01
  rw [← hh'] at hval
  have hb' : h' ∈ adelicBorel (𝓞 L) L := by
    show (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
    rw [hval]; simp
  have e1 : w * (h * y) = h' * (w * y) := by rw [hh']; group
  rw [e1, adelicHeight_borel_mul L hb, adelicHeight_borel_mul L hb']
  have hF : borelDiagFst (⟨h', hb'⟩ : ↥(adelicBorel (𝓞 L) L)) = borelDiagSnd (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L)) := by
    apply Units.ext
    rw [borelDiagFst_apply_val, borelDiagSnd_apply_val]
    show (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = _
    rw [hval]; simp
  have hS : borelDiagSnd (⟨h', hb'⟩ : ↥(adelicBorel (𝓞 L) L)) = borelDiagFst (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L)) := by
    apply Units.ext
    rw [borelDiagFst_apply_val, borelDiagSnd_apply_val]
    show (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = _
    rw [hval]; simp
  rw [hF, hS]
  have h1 : 0 < ideleNorm L (borelDiagFst (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L))) := ideleNorm_pos _
  have h2 : 0 < ideleNorm L (borelDiagSnd (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L))) := ideleNorm_pos _
  field_simp

def hgt (y : AdelicGL2 (𝓞 L) L) : ℝ := adelicHeight L y * adelicHeight L (adelicWeyl (𝓞 L) L * y)

theorem hgt_pos (y : AdelicGL2 (𝓞 L) L) : 0 < hgt L y := mul_pos (adelicHeight_pos y) (adelicHeight_pos _)

theorem continuous_hgt : Continuous (hgt L) :=
  (NumberField.AdelicHeight.continuous_adelicHeight L).mul
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp (continuous_const.mul continuous_id))

theorem hgt_diag_mul (h y : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    hgt L (h * y) = hgt L y := height_prod_diag_mul L h y h10 h01

theorem neg_log_sub_log_eq (y : AdelicGL2 (𝓞 L) L) :
    -Real.log (adelicHeight L y) - Real.log (adelicHeight L (adelicWeyl (𝓞 L) L * y)) = -Real.log (hgt L y) := by
  rw [hgt, Real.log_mul (adelicHeight_pos y).ne' (adelicHeight_pos _).ne']
  ring

end Height

section Algebra

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := rfl

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem centralScalar_val (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![(z : AdeleRing (𝓞 L) L), 0; 0, (z : AdeleRing (𝓞 L) L)] := by
  ext i j
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j = _
  fin_cases i <;> fin_cases j <;> simp

theorem centralScalar_inv_val (z : (AdeleRing (𝓞 L) L)ˣ) :
    (((centralScalar (𝓞 L) L z)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 =
      ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
  rw [← map_inv, centralScalar_val]; simp

theorem continuous_matrix_two {A X : Type*} [TopologicalSpace A] [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) A}
    (h00 : Continuous fun x => f x 0 0) (h01 : Continuous fun x => f x 0 1)
    (h10 : Continuous fun x => f x 1 0) (h11 : Continuous fun x => f x 1 1) : Continuous f := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine (continuous_matrix_two ?_ ?_ ?_ ?_ :
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
        (!![(z : AdeleRing (𝓞 L) L), 0; 0, (z : AdeleRing (𝓞 L) L)] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).congr
      fun z => (centralScalar_val z).symm
    · simpa using Units.continuous_val
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using Units.continuous_val
  · refine (continuous_matrix_two ?_ ?_ ?_ ?_ :
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
        (!![((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 0; 0, ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)] :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).congr
      fun z => ?_
    · simpa using Units.continuous_coe_inv
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using Units.continuous_coe_inv
    · show _ = (((centralScalar (𝓞 L) L z)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      rw [← map_inv, centralScalar_val]

theorem continuous_val_apply (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_val_inv_apply (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 L) L => ((g⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j :=
  Units.continuous_coe_inv.matrix_elem i j

theorem continuous_unitsAct (τ : L ≃ₐ[K] L) : Continuous (D.unitsAct τ : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) :=
  Continuous.units_map _ (D.continuous_act τ)

theorem unitsAct_inv_apply (w : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ⁻¹ (D.unitsAct σ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem unitsAct_unitsAct_inv (w : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ (D.unitsAct σ⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem exists_isCompact_centralScalar_mem (M : Set (AdelicGL2 (𝓞 L) L)) (hM : IsCompact M) :
    ∃ S : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact S ∧ ∀ u : (AdeleRing (𝓞 L) L)ˣ, centralScalar (𝓞 L) L u ∈ M → u ∈ S := by
  set v : AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L := fun g => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hv
  set vi : AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L :=
    fun g => ((g⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hvi
  refine ⟨(Units.embedProduct (AdeleRing (𝓞 L) L)) ⁻¹' ((v '' M) ×ˢ (MulOpposite.op '' (vi '' M))), ?_, ?_⟩
  · exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hM.image (continuous_val_apply 0 0)).prod ((hM.image (continuous_val_inv_apply 0 0)).image
        MulOpposite.continuous_op))
  · intro u hu
    rw [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    refine ⟨⟨_, hu, ?_⟩, ⟨vi (centralScalar (𝓞 L) L u), ⟨_, hu, rfl⟩, ?_⟩⟩
    · show ((centralScalar (𝓞 L) L u : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = u
      rw [centralScalar_val]; simp
    · show MulOpposite.op ((((centralScalar (𝓞 L) L u)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0) = _
      rw [centralScalar_inv_val]

end Algebra

section Invariance

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

def xiTop (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ where
  toFun z := ξL ⟨z, Subgroup.mem_top z⟩
  map_one' := by exact map_one ξL
  map_mul' a b := by rw [← map_mul]; rfl

theorem xiTop_apply (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    xiTop ξL z = ξL ⟨z, Subgroup.mem_top z⟩ := rfl

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (δ₀ : GL (Fin 2) L) (φ : AdelicGL2 (𝓞 L) L → ℂ)

def orb (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ∂νZL

theorem orb_mul_eq (g y : AdelicGL2 (𝓞 L) L) (m : (AdeleRing (𝓞 L) L)ˣ)
    (hg : g⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ g =
      globalPoints (𝓞 L) L δ₀ * centralScalar (𝓞 L) L m) :
    orb νZL D σ ξL δ₀ φ (g * y) =
      (((xiTop ξL (D.unitsAct σ⁻¹ m))⁻¹ : ℂˣ) : ℂ) * orb νZL D σ ξL δ₀ φ y :=
  AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
    K L D σ νZL (xiTop ξL) φ _ g y m hg

theorem val_mul_apply (x y : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((x * y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 0 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 1 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem diag_comm (x y : AdelicGL2 (𝓞 L) L)
    (hx10 : (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) (hx01 : (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hy10 : (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) (hy01 : (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    x * y = y * x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [val_mul_apply, val_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [hx10, hx01, hy10, hy01, mul_comm]

def diagUnit11 (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) : (AdeleRing (𝓞 L) L)ˣ :=
  borelDiagSnd (⟨h, h10⟩ : ↥(adelicBorel (𝓞 L) L))

include δ₀ in
omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
theorem coe_diagUnit11 (h : AdelicGL2 (𝓞 L) L) (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) :
    ((diagUnit11 h h10 : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 := rfl

variable (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
  (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)

include hξσ hδ₀u hδ₀l in

theorem orb_mul_of_diag_of_mem_center (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))
    (y : AdelicGL2 (𝓞 L) L) :
    orb νZL D σ ξL δ₀ φ (h * y) = orb νZL D σ ξL δ₀ φ y := by
  set gp := globalPoints (𝓞 L) L with hgp
  set sh := sigmaAdelicAct K L D σ h with hsh
  have hcen' := hcen
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen'
  obtain ⟨mm, hmm⟩ := hcen'
  have hmm' : centralScalar (𝓞 L) L mm = sh * h⁻¹ := hmm
  have hcs : centralScalar (𝓞 L) L mm ∈ Subgroup.center (AdelicGL2 (𝓞 L) L) := by
    rw [hmm']; exact hcen
  have e1 : sh = centralScalar (𝓞 L) L mm * h := by rw [hmm', inv_mul_cancel_right]
  have e2 : gp δ₀ * h = h * gp δ₀ := by
    refine diag_comm _ _ ?_ ?_ h10 h01
    · show algebraMap L (AdeleRing (𝓞 L) L) ((δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0) = 0
      rw [hδ₀u, map_zero]
    · show algebraMap L (AdeleRing (𝓞 L) L) ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1) = 0
      rw [hδ₀l, map_zero]
  have e3 : centralScalar (𝓞 L) L mm * h = h * centralScalar (𝓞 L) L mm :=
    (Subgroup.mem_center_iff.1 hcs h).symm
  have key : h⁻¹ * gp δ₀ * sh = gp δ₀ * centralScalar (𝓞 L) L mm := by
    calc h⁻¹ * gp δ₀ * sh = h⁻¹ * gp δ₀ * (centralScalar (𝓞 L) L mm * h) := by rw [e1]
      _ = h⁻¹ * (gp δ₀ * h) * centralScalar (𝓞 L) L mm := by rw [e3]; group
      _ = gp δ₀ * centralScalar (𝓞 L) L mm := by rw [e2]; group
  rw [orb_mul_eq νZL D σ ξL δ₀ φ h y mm key]

  set hu : (AdeleRing (𝓞 L) L)ˣ := diagUnit11 h h10 with hhu
  have hmm_eq : mm = D.unitsAct σ hu * hu⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    have hval := congrArg (fun M : AdelicGL2 (𝓞 L) L => (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1) e1
    rw [hsh, sigmaAdelicAct_apply, val_mul_apply, centralScalar_val] at hval
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', zero_mul, zero_add] at hval
    rw [Units.val_mul]
    exact hval.symm
  have hx1 : ξL ⟨D.unitsAct σ⁻¹ mm, Subgroup.mem_top _⟩ = ξL ⟨mm, Subgroup.mem_top _⟩ := by
    have h1 := hξσ (D.unitsAct σ⁻¹ mm)
    rw [unitsAct_unitsAct_inv] at h1
    exact h1.symm
  have htriv : xiTop ξL (D.unitsAct σ⁻¹ mm) = 1 := by
    rw [xiTop_apply, hx1, ← xiTop_apply, hmm_eq, map_mul (xiTop ξL), map_inv (xiTop ξL), xiTop_apply, xiTop_apply,
      hξσ hu, mul_inv_cancel]
  rw [htriv, inv_one, Units.val_one, one_mul]

end Invariance

section Continuity

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (δ₀ : GL (Fin 2) L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)

theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

include hξc hφc hφs in

theorem continuous_orb : Continuous (orb νZL D σ ξL δ₀ φ) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := locallyCompactSpace_ideles
  set gp := globalPoints (𝓞 L) L with hgp
  set σA := sigmaAdelicAct K L D σ with hσA
  set cs := centralScalar (𝓞 L) L with hcs
  set I : AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun y z =>
    ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * gp δ₀ * σA (cs z * y)) with hI
  have harg : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => p.1⁻¹ * gp δ₀ * σA (cs p.2 * p.1) :=
    ((continuous_fst.inv).mul continuous_const).mul
      ((continuous_sigmaAdelicAct K L D σ).comp ((continuous_centralScalar.comp continuous_snd).mul continuous_fst))
  have hIc : Continuous (Function.uncurry I) := (hξc.comp continuous_snd).mul (hφc.comp harg)
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds y₀
  set C := tsupport φ with hC
  have hCc : IsCompact C := hφs.isCompact
  set M : Set (AdelicGL2 (𝓞 L) L) :=
    (fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => (gp δ₀)⁻¹ * p.1 * p.2.1 * p.2.2⁻¹) ''
      (N ×ˢ C ×ˢ (σA '' N)) with hM
  have hMc : IsCompact M :=
    (hNc.prod (hCc.prod (hNc.image (continuous_sigmaAdelicAct K L D σ)))).image
      (((continuous_const.mul continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
        (continuous_snd.comp continuous_snd).inv)
  obtain ⟨S, hSc, hS⟩ := exists_isCompact_centralScalar_mem M hMc
  set S' : Set (AdeleRing (𝓞 L) L)ˣ := (D.unitsAct σ⁻¹) '' S with hS'
  have hS'c : IsCompact S' := hSc.image (continuous_unitsAct D σ⁻¹)
  have hvanish : ∀ y ∈ N, ∀ z ∉ S', I y z = 0 := by
    intro y hy z hz
    by_contra hne
    apply hz
    have hφne : φ (y⁻¹ * gp δ₀ * σA (cs z * y)) ≠ 0 := right_ne_zero_of_mul hne
    have hmem : y⁻¹ * gp δ₀ * σA (cs z * y) ∈ C := subset_tsupport _ (Function.mem_support.2 hφne)
    have hcsM : cs (D.unitsAct σ z) ∈ M := by
      refine ⟨(y, y⁻¹ * gp δ₀ * σA (cs z * y), σA y), ⟨hy, hmem, ⟨y, hy, rfl⟩⟩, ?_⟩
      show (gp δ₀)⁻¹ * y * (y⁻¹ * gp δ₀ * σA (cs z * y)) * (σA y)⁻¹ = cs (D.unitsAct σ z)
      rw [hcs, ← sigmaAdelicAct_centralScalar D σ, ← hσA, map_mul]
      group
    exact ⟨D.unitsAct σ z, hS _ hcsM, unitsAct_inv_apply D σ z⟩
  have heq : ∀ y ∈ N, ∫ z in S', I y z ∂νZL = orb νZL D σ ξL δ₀ φ y := fun y hy =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hvanish y hy z hz
  have hcont : Continuous fun y => ∫ z in S', I y z ∂νZL := continuous_parametric_integral_of_continuous hIc hS'c
  refine (hcont.continuousAt (x := y₀)).congr ?_
  filter_upwards [hN] with y hy
  exact heq y hy

end Continuity

section Main

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 (L : Type) [Field L] [NumberField L] : BorelSpace (AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_adelicGL2

theorem fibre_lower_bound {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    (H₀ : Set H) (hH₀m : MeasurableSet H₀) (f : G → ℝ≥0∞) (c : ℝ≥0∞) (y : G) (g₀ : H)
    (hval : ∀ x : H, x * g₀ ∈ H₀ → c ≤ f ((x : G) * y)) :
    μH H₀ * c ≤ ∫⁻ x : H, f ((x : G) * y) ∂μH := by
  have hTm : MeasurableSet ((fun x : H => x * g₀) ⁻¹' H₀) := hH₀m.preimage (measurable_mul_const g₀)
  calc μH H₀ * c = μH ((fun x : H => x * g₀) ⁻¹' H₀) * c := by rw [measure_preimage_mul_right μH g₀ H₀]
    _ = ∫⁻ x in (fun x : H => x * g₀) ⁻¹' H₀, c ∂μH := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in (fun x : H => x * g₀) ⁻¹' H₀, f ((x : G) * y) ∂μH := setLIntegral_mono' hTm fun x hx => hval x hx
    _ ≤ ∫⁻ x, f ((x : G) * y) ∂μH := setLIntegral_le_lintegral _ _

theorem orbint
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => orb νZL D σ ξL δ₀ φ q.out)
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
          ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) *
            orb νZL D σ ξL δ₀ φ q.out)
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∃ M : ℝ, ∀ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), orb νZL D σ ξL δ₀ φ q.out ≠ 0 →
        NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L) *
          NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L)) ≤ M := by
  classical

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : LocallyCompactSpace H := hHc.locallyCompactSpace
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set νQ := HaarQuotient.measure μ H μH with hνQ
  set F : AdelicGL2 (𝓞 L) L → ℂ := orb νZL D σ ξL δ₀ φ with hF
  set w := adelicWeyl (𝓞 L) L with hw

  have hFinv : ∀ h ∈ H, ∀ y, F (h * y) = F y := by
    intro h hh y
    obtain ⟨h10, h01, hcen⟩ := (hH h).1 hh
    exact orb_mul_of_diag_of_mem_center νZL D σ ξL δ₀ φ hξσ hδ₀u hδ₀l h h10 h01 hcen y
  have hFcont : Continuous F := continuous_orb νZL D σ ξL hξc δ₀ φ hφc hφs
  obtain ⟨C', hC'c, hC'⟩ :=
    AutomorphicForm.exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
      K L σ hgen D H hH δ₀ hδ₀u hδ₀l hreg (tsupport φ) hφs.isCompact
  have hsupp : ∀ y, F y ≠ 0 → ∃ h k : AdelicGL2 (𝓞 L) L, h ∈ H ∧ k ∈ C' ∧ y = h * k := by
    intro y hy
    have hex : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
        φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hy
      show (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ∂νZL) = 0
      simp only [hall, mul_zero, integral_zero]
    obtain ⟨z, hz⟩ := hex
    exact hC' y z (subset_tsupport _ (Function.mem_support.2 hz))

  have hgtH : ∀ h ∈ H, ∀ y, hgt L (h * y) = hgt L y := by
    intro h hh y
    obtain ⟨h10, h01, -⟩ := (hH h).1 hh
    exact hgt_diag_mul L h y h10 h01
  obtain ⟨Mh, hMh⟩ : ∃ Mh : ℝ, ∀ k ∈ C', hgt L k ≤ Mh := by
    obtain ⟨B, hB⟩ := hC'c.exists_bound_of_continuousOn (continuous_hgt L).continuousOn
    exact ⟨B, fun k hk => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB k hk))⟩
  obtain ⟨mh, hmh0, hmh⟩ : ∃ mh : ℝ, 0 < mh ∧ ∀ k ∈ C', mh ≤ hgt L k := by
    rcases C'.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨k₀, hk₀, hmin⟩ := hC'c.exists_isMinOn h (continuous_hgt L).continuousOn
      exact ⟨hgt L k₀, hgt_pos L k₀, fun k hk => hmin hk⟩
  have h3 : ∀ y, F y ≠ 0 → hgt L y ≤ Mh := by
    intro y hy
    obtain ⟨h, k, hh, hk, rfl⟩ := hsupp y hy
    rw [hgtH h hh]; exact hMh k hk
  set B : ℝ := max |Real.log mh| |Real.log Mh| with hB
  have hlog : ∀ y, F y ≠ 0 → |Real.log (hgt L y)| ≤ B := by
    intro y hy
    obtain ⟨h, k, hh, hk, rfl⟩ := hsupp y hy
    rw [hgtH h hh]
    have h1 : Real.log mh ≤ Real.log (hgt L k) := Real.log_le_log hmh0 (hmh k hk)
    have h2 : Real.log (hgt L k) ≤ Real.log Mh := Real.log_le_log (hgt_pos L k) (hMh k hk)
    exact abs_le_max_abs_abs h1 h2

  have hout : ∀ y : AdelicGL2 (𝓞 L) L, ∃ h ∈ H,
      ((Quotient.mk'' y : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L)).out : AdelicGL2 (𝓞 L) L) = h * y := by
    intro y
    have h1 : (MulAction.orbitRel H (AdelicGL2 (𝓞 L) L))
        ((Quotient.mk'' y : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L)).out) y := Quotient.mk_out y
    rw [MulAction.orbitRel_apply] at h1
    obtain ⟨h, hh⟩ := h1
    exact ⟨h, h.2, hh.symm⟩
  have hmeasQ : ∀ f : AdelicGL2 (𝓞 L) L → ℂ, Continuous f → (∀ h ∈ H, ∀ y, f (h * y) = f y) →
      Measurable fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => f q.out := by
    intro f hf hinv
    rw [measurable_from_quotient]
    have hcomp : ((fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => f q.out) ∘ Quotient.mk'') = f := by
      funext y
      obtain ⟨h, hh, e⟩ := hout y
      simp only [Function.comp_apply]
      rw [e, hinv h hh]
    rw [hcomp]
    exact hf.measurable

  obtain ⟨H₀, hH₀c, hH₀n⟩ := exists_compact_mem_nhds (1 : H)
  have hκ0 : μH H₀ ≠ 0 := (Measure.measure_pos_of_mem_nhds μH hH₀n).ne'
  have hκtop : μH H₀ ≠ ⊤ := hH₀c.measure_lt_top.ne
  set U : Set (AdelicGL2 (𝓞 L) L) := (Subtype.val '' H₀) * C' with hU
  have hUc : IsCompact U := (hH₀c.image continuous_subtype_val).mul hC'c
  have hUm : MeasurableSet U := hUc.isClosed.measurableSet
  obtain ⟨BF, hBF⟩ := hUc.exists_bound_of_continuousOn hFcont.continuousOn
  set f : AdelicGL2 (𝓞 L) L → ℝ≥0∞ := fun g => ‖F g‖ₑ * U.indicator 1 g with hf
  have hfm : Measurable f := hFcont.measurable.enorm.mul (measurable_one.indicator hUm)
  have hfib : ∀ y : AdelicGL2 (𝓞 L) L, μH H₀ * ‖F y‖ₑ ≤ ∫⁻ x : H, f ((x : AdelicGL2 (𝓞 L) L) * y) ∂μH := by
    intro y
    by_cases hy : F y = 0
    · simp [hy]
    obtain ⟨h, k, hh, hk, hyk⟩ := hsupp y hy
    refine fibre_lower_bound H μH H₀ hH₀c.isClosed.measurableSet f _ y ⟨h, hh⟩ fun x hx => le_of_eq ?_
    have hxU : (x : AdelicGL2 (𝓞 L) L) * y ∈ U := by
      rw [hyk, ← mul_assoc]
      exact Set.mul_mem_mul ⟨_, hx, by rw [Subgroup.coe_mul]⟩ hk
    simp only [hf, Set.indicator_of_mem hxU, Pi.one_apply, mul_one]
    rw [hFinv _ x.2]
  have hWeil := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hHc μH f hfm
  have hfle : ∀ g, f g ≤ ENNReal.ofReal BF * U.indicator 1 g := by
    intro g
    by_cases hg : g ∈ U
    · simp only [hf, Set.indicator_of_mem hg, Pi.one_apply, mul_one]
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hBF g hg)
    · simp [hf, hg]
  have hIf : ∫⁻ g, f g ∂μ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono hfle) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one hUm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUc.measure_lt_top
  have hlin : ∫⁻ q, ‖F q.out‖ₑ ∂νQ < ⊤ := by
    have h1 : μH H₀ * ∫⁻ q, ‖F q.out‖ₑ ∂νQ ≤ ∫⁻ g, f g ∂μ := by
      rw [← lintegral_const_mul' _ _ hκtop, hWeil]
      exact lintegral_mono fun q => hfib q.out
    have h2 : μH H₀ * ∫⁻ q, ‖F q.out‖ₑ ∂νQ < ⊤ := lt_of_le_of_lt h1 hIf
    rcases ENNReal.mul_lt_top_iff.1 h2 with h | h | h
    · exact h.2
    · exact absurd h hκ0
    · rw [h]; exact ENNReal.zero_lt_top
  have hInt1 : Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => F q.out) νQ :=
    ⟨(hmeasQ F hFcont hFinv).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 hlin⟩

  set Wt : AdelicGL2 (𝓞 L) L → ℂ := fun y =>
    ((-Real.log (adelicHeight L y) - Real.log (adelicHeight L (w * y)) : ℝ) : ℂ) with hWt
  have hWt' : ∀ y, Wt y = ((-Real.log (hgt L y) : ℝ) : ℂ) := fun y => by rw [hWt]; simp only; rw [neg_log_sub_log_eq]
  have hWtc : Continuous Wt := by
    have : Wt = fun y => ((-Real.log (hgt L y) : ℝ) : ℂ) := funext hWt'
    rw [this]
    exact Complex.continuous_ofReal.comp (((continuous_hgt L).log fun y => (hgt_pos L y).ne').neg)
  have hG2c : Continuous fun y => Wt y * F y := hWtc.mul hFcont
  have hG2inv : ∀ h ∈ H, ∀ y, Wt (h * y) * F (h * y) = Wt y * F y := by
    intro h hh y
    rw [hWt', hWt', hgtH h hh, hFinv h hh]
  have hInt2 : Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => Wt q.out * F q.out) νQ := by
    refine Integrable.mono' (hInt1.norm.const_mul B)
      (hmeasQ (fun y => Wt y * F y) hG2c hG2inv).aestronglyMeasurable (ae_of_all _ fun q => ?_)
    by_cases hq : F q.out = 0
    · simp [hq]
    · rw [norm_mul, hWt', Complex.norm_real, Real.norm_eq_abs, abs_neg]
      exact mul_le_mul_of_nonneg_right (hlog _ hq) (norm_nonneg _)
  exact ⟨hInt1, hInt2, ⟨Mh, fun q hq => h3 q.out hq⟩⟩

end Main

end R1S80OrbInt

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
          ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∃ M : ℝ, ∀ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL) ≠ 0 →
        NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L) *
          NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L)) ≤ M :=
  R1S80OrbInt.orbint K L νZL D σ hgen ξL hξc H hHc hH μH hξσ δ₀ hδ₀u hδ₀l hreg φ hφc hφs

end

end S_AutomorphicForm_integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one
end P2MW
export P2MW.S_AutomorphicForm_integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one (solution)
