-- Prove2me | solution 1 for AutomorphicForm.rightConv_translate_package_of_isCuspAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/49c1b341-f424-5491-840d-f53d8ae28556

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightConv_translate_package_of_isCuspAutomorphicFnAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ws23
namespace C6AB
open Matrix MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AdelicDock UnramifiedWhittaker

variable (F : Type) [Field F] [NumberField F]

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

theorem map_unipotentGL2_integers (v : HeightOneSpectrum (𝓞 F)) (r : v.adicCompletionIntegers F) :
    Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (unipotentGL2 r) =
      unipotentGL2 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2]

theorem unipotent_eq_unipotentGL2 {K : Type*} [Field K] (x : K) : unipotent x = unipotentGL2 x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [unipotent, unipotentGL2]

noncomputable def adeleAt (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : AdeleRing (𝓞 F) F :=
  ((0 : InfiniteAdeleRing F), splice (𝓞 F) F v 0 x)

theorem splice_apply_eq_self (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) :
    splice (𝓞 F) F v a (a v) = a := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  by_cases hw : w = v
  · subst hw
    exact splice_apply_self (𝓞 F) F w a (a w)
  · exact splice_apply_of_ne (𝓞 F) F v a (a v) hw

theorem coe_placeEmbed_apply (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    ((placeEmbed F v k : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
          ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j)) : AdeleRing (𝓞 F) F) := by
  rfl

theorem placeEmbed_unipotent (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    placeEmbed F v (unipotent x) = unipotentGL2 (adeleAt F v x) := by
  refine Units.ext ?_
  ext i j
  rw [coe_placeEmbed_apply, unipotentGL2_coe]
  have hu : ((unipotent x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      !![1, x; 0, 1] := rfl
  rw [hu]
  have h1 : splice (𝓞 F) F v (1 : FiniteAdeleRing (𝓞 F) F) 1 = 1 := by
    have := splice_apply_eq_self F v 1
    exact this
  have h0 : splice (𝓞 F) F v (0 : FiniteAdeleRing (𝓞 F) F) 0 = 0 := by
    have := splice_apply_eq_self F v 0
    exact this
  fin_cases i <;> fin_cases j
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) ((!![(1 : v.adicCompletion F), x; 0, 1]) 0 0)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 0 0
    simp only [Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    rw [h1]
    rfl
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 1, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1) ((!![(1 : v.adicCompletion F), x; 0, 1]) 0 1)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 0 1
    simp only [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rfl
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) ((!![(1 : v.adicCompletion F), x; 0, 1]) 1 0)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 1 0
    simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h0]
    rfl
  · show (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1, splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) ((!![(1 : v.adicCompletion F), x; 0, 1]) 1 1)) : AdeleRing (𝓞 F) F) = !![(1 : AdeleRing (𝓞 F) F), adeleAt F v x; 0, 1] 1 1
    simp only [Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h1]
    rfl

theorem gl_eq_of_components (g h : GL (Fin 2) (AdeleRing (𝓞 F) F)) (harch : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w (glFin (𝓞 F) F g) =
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h)) : g = h := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_)
  · exact congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing F) => (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) harch
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    exact congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => (x : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) (hfin w)

theorem placeEmbed_mul_comm_of_finComponent_eq_one (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F))
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) :
    placeEmbed F v k * g = g * placeEmbed F v k := by
  refine gl_eq_of_components F _ _ ?_ fun w => ?_
  · rw [map_mul, map_mul, placeEmbed, MonoidHom.comp_apply, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, map_mul, map_mul, placeEmbed, MonoidHom.comp_apply, glFin_finEmbed]
    by_cases hw : w = v
    · subst hw
      rw [hg, mul_one, one_mul]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F _ k hw, one_mul, mul_one]

end Ws23.C6AB

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (g₀ : AdelicGL2 (𝓞 F) F) :
    Continuous (rightConv F φ (fun y => f (g₀⁻¹ * y))) ∧
    (∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖rightConv F φ (fun y => f (g₀⁻¹ * y)) g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M) ∧
    (∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ (fun y => f (g₀⁻¹ * y)) (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) =
        rightConv F φ (fun y => f (g₀⁻¹ * y)) g) ∧
    (∀ g : AdelicGL2 (𝓞 F) F, rightConv F φ (fun y => f (g₀⁻¹ * y)) g = rightConv F φ f (g * g₀)) ∧
    (∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ (rightConv F φ (fun y => f (g₀⁻¹ * y))) 1 g =
        whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ (rightConv F φ f) 1 (g * g₀)) ∧
    (∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = rightConv F φ f g) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have hf' : IsFactorizableTestFn F (fun y => f (g₀⁻¹ * y)) :=
    AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F f hf g₀
  have hLs := ((lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1).1
  have key : ∀ (f' : AdelicGL2 (𝓞 F) F → ℂ) (β : F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f' (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = rightConv F φ f' g := by
    intro f' β g
    rw [← rightConv_comp_mul_left]
    congr 1
    funext y
    rw [← Ws23.C6AB.globalPoints_unipotentGL2, hLs.left_invariant]
  refine ⟨(AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont _ hf').1,
    AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow F c u d₁ d₂ T hd hcov ξ φ hφ hcont _ hf',
    key _, fun g => (AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ f g g₀).symm, ?_,
    key f⟩
  intro g
  simp only [whittakerCoefficient]
  congr 1
  funext y
  rw [← mul_assoc, AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ f (unipotentGL2 y * g) g₀]

end S_AutomorphicForm_rightConv_translate_package_of_isCuspAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_rightConv_translate_package_of_isCuspAutomorphicFnAt (solution)
