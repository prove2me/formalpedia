-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/00aa4e33-796d-56f2-a3ce-0fbeff00371f

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
p2m_open "AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm.CuspidalConstituent"
open scoped NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rightConv rightConv_apply IsArchTestFactor IsFinTestFactor IsFactorizableTestFn continuous_and_hasCompactSupport_of_isFactorizableTestFn"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "rightTranslate rightTranslate_apply levelInvariantSubmodule"
namespace LevelIndicatorAux
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private def finMatFun (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, m i j)

private def archMatFun (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => (a i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private theorem finMatFun_map_arch (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (finMatFun F m).map (adeleArch (𝓞 F) F) = 1 := by
  ext i j; rfl

private theorem finMatFun_map_fin (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (finMatFun F m).map (adeleFin (𝓞 F) F) = m := by
  ext i j; rfl

private theorem archMatFun_map_arch (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (archMatFun F a).map (adeleArch (𝓞 F) F) = a := by
  ext i j; rfl

private theorem archMatFun_map_fin (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (archMatFun F a).map (adeleFin (𝓞 F) F) = 1 := by
  ext i j; rfl

private theorem matrix_ext_of_map {M M' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (h₁ : M.map (adeleArch (𝓞 F) F) = M'.map (adeleArch (𝓞 F) F))
    (h₂ : M.map (adeleFin (𝓞 F) F) = M'.map (adeleFin (𝓞 F) F)) : M = M' := by
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j

private def finMat :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) where
  toFun := finMatFun F
  map_one' := matrix_ext_of_map F
    (by rw [finMatFun_map_arch, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [finMatFun_map_fin, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' m m' := matrix_ext_of_map F
    (by rw [Matrix.map_mul, finMatFun_map_arch, finMatFun_map_arch, finMatFun_map_arch, Matrix.mul_one])
    (by rw [Matrix.map_mul, finMatFun_map_fin, finMatFun_map_fin, finMatFun_map_fin])

private def archMat :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →* Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) where
  toFun := archMatFun F
  map_one' := matrix_ext_of_map F
    (by rw [archMatFun_map_arch, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [archMatFun_map_fin, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' a a' := matrix_ext_of_map F
    (by rw [Matrix.map_mul, archMatFun_map_arch, archMatFun_map_arch, archMatFun_map_arch])
    (by rw [Matrix.map_mul, archMatFun_map_fin, archMatFun_map_fin, archMatFun_map_fin, Matrix.mul_one])

@[scoped simp] private theorem finMat_apply (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finMat F m = finMatFun F m := rfl

@[scoped simp] private theorem archMat_apply (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    archMat F a = archMatFun F a := rfl

private theorem archMatFun_mul_finMatFun (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    archMatFun F a * finMatFun F m = fun i j => (a i j, m i j) := by
  refine matrix_ext_of_map F ?_ ?_
  · rw [Matrix.map_mul, archMatFun_map_arch, finMatFun_map_arch, Matrix.mul_one]; ext i j; rfl
  · rw [Matrix.map_mul, archMatFun_map_fin, finMatFun_map_fin, Matrix.one_mul]; ext i j; rfl

private theorem finMatFun_mul_archMatFun (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finMatFun F m * archMatFun F a = fun i j => (a i j, m i j) := by
  refine matrix_ext_of_map F ?_ ?_
  · rw [Matrix.map_mul, archMatFun_map_arch, finMatFun_map_arch, Matrix.one_mul]; ext i j; rfl
  · rw [Matrix.map_mul, archMatFun_map_fin, finMatFun_map_fin, Matrix.mul_one]; ext i j; rfl

private def finLift : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin 2) (AdeleRing (𝓞 F) F) :=
  Units.map (finMat F)

private def archLift : GL (Fin 2) (InfiniteAdeleRing F) →* GL (Fin 2) (AdeleRing (𝓞 F) F) :=
  Units.map (archMat F)

private theorem glFin_finLift (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (finLift F m) = m := by
  ext i j : 2
  rfl

private theorem glArch_finLift (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (finLift F m) = 1 := by
  ext i j : 2
  rfl

private theorem glArch_archLift (a : GL (Fin 2) (InfiniteAdeleRing F)) :
    glArch (𝓞 F) F (archLift F a) = a := by
  ext i j : 2
  rfl

private theorem glFin_archLift (a : GL (Fin 2) (InfiniteAdeleRing F)) :
    glFin (𝓞 F) F (archLift F a) = 1 := by
  ext i j : 2
  rfl

private theorem archLift_mul_finLift (y : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    archLift F (glArch (𝓞 F) F y) * finLift F (glFin (𝓞 F) F y) = y := by
  refine Units.ext ?_
  show archMatFun F _ * finMatFun F _ = _
  rw [archMatFun_mul_finMatFun]
  rfl

private theorem archLift_mul_finLift_comm (a : GL (Fin 2) (InfiniteAdeleRing F))
    (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    archLift F a * finLift F m = finLift F m * archLift F a := by
  refine Units.ext ?_
  show archMatFun F _ * finMatFun F _ = finMatFun F _ * archMatFun F _
  rw [archMatFun_mul_finMatFun, finMatFun_mul_archMatFun]

private theorem finLift_mem_finiteAdelicGL2Subgroup (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finLift F m ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact glArch_finLift F m

private theorem finLift_mem_levelOne_inf {N : Ideal (𝓞 F)} {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finiteLevelOne (𝓞 F) F N) :
    finLift F k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine ⟨?_, finLift_mem_finiteAdelicGL2Subgroup F k⟩
  show glFin (𝓞 F) F (finLift F k) ∈ finiteLevelOne (𝓞 F) F N
  rwa [glFin_finLift]

private theorem image_glFin_levelOne_inf (N : Ideal (𝓞 F)) :
    (glFin (𝓞 F) F) '' (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (GL (Fin 2) (AdeleRing (𝓞 F) F)))
      = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.1
  · intro hm
    exact ⟨finLift F m, finLift_mem_levelOne_inf F hm, glFin_finLift F m⟩

private theorem continuous_finMat : Continuous (finMat F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_const.prodMk ((continuous_apply j).comp (continuous_apply i))

private theorem continuous_archMat : Continuous (archMat F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((continuous_apply j).comp (continuous_apply i)).prodMk continuous_const

private theorem continuous_finLift : Continuous (finLift F) :=
  Continuous.units_map (finMat F) (continuous_finMat F)

private theorem continuous_archLift : Continuous (archLift F) :=
  Continuous.units_map (archMat F) (continuous_archMat F)

end AutomorphicForm.CuspidalConstituent.LevelIndicatorAux
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm.CuspidalConstituent.LevelIndicatorAux"
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm.CuspidalConstituent"
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.AutomorphicForm.CuspidalConstituent.LevelIndicatorAux"

open AutomorphicForm.CuspidalConstituent.LevelIndicatorAux in
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Continuous Ψ)
    (hΨN : Ψ ∈ levelInvariantSubmodule F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B) N)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) *
        Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B).U N : Set (AdelicGL2 (𝓞 F) F)))
          (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F y)) ∧
    rightConv F Ψ (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) ∈
      Submodule.span ℂ ((fun g => rightTranslate F g (rightConv F Ψ
        (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F y)))) ''
        (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) := by
  classical

  have hK : (AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B).U N : Set (AdelicGL2 (𝓞 F) F))
      = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    image_glFin_levelOne_inf F N
  rw [hK]
  set Kf : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := finiteLevelOne (𝓞 F) F N with hKf
  have hKopen : IsOpen (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isOpen_finiteLevelOne (𝓞 F) F hN
  have hKcomp : IsCompact (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isCompact_finiteLevelOne (𝓞 F) F N
  have hKclosed : IsClosed (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isClosed_finiteLevelOne (𝓞 F) F N

  have hind_lc : IsLocallyConstant ((Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    · exact ⟨Kf, hKopen, hx, fun b hb => by rw [Set.indicator_of_mem hb, Set.indicator_of_mem hx]⟩
    · exact ⟨(Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))ᶜ, hKclosed.isOpen_compl, hx, fun b hb => by
        rw [Set.indicator_of_notMem (Set.notMem_of_mem_compl hb), Set.indicator_of_notMem hx]⟩
  have hind_cs : HasCompactSupport ((Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hKcomp fun b hb => Set.indicator_of_notMem hb _
  refine ⟨⟨fa, _, hfa, ⟨hind_lc, hind_cs⟩, fun g => rfl⟩, ?_⟩

  set f : AdelicGL2 (𝓞 F) F → ℂ :=
    fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y) with hf
  set f₀ : AdelicGL2 (𝓞 F) F → ℂ := fun y => fa (AdelicLevel.glArch (𝓞 F) F y) *
    Set.indicator (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F y) with hf₀

  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := ⟨rfl⟩
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : LocallyCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
      inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
    infer_instance
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := by
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
      inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
    infer_instance
  set μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haar with hμa
  set μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Measure.haar with hμf
  obtain ⟨c, hc, hsplit⟩ :=
    NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral F μa μf

  obtain ⟨t, ht⟩ := hff.2.elim_finite_subcover
    (fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (fun z => b⁻¹ * z) ⁻¹' (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))))
    (fun b => hKopen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  set Q : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) :=
    Finset.image (fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (QuotientGroup.mk b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf)) t with hQ
  have hcover : ∀ b, ff b ≠ 0 → (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) ∈ Q := by
    intro b hb
    have hb' : b ∈ tsupport ff := subset_tsupport _ (Function.mem_support.2 hb)
    obtain ⟨g, hg, hgb⟩ := Set.mem_iUnion₂.1 (ht hb')
    exact Finset.mem_image.2 ⟨g, hg, QuotientGroup.eq.2 hgb⟩

  set χ : (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) → GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun q b => if (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) = q then 1 else 0 with hχ
  have hχ_lc : ∀ q, IsLocallyConstant (χ q) := by
    intro q
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    refine ⟨(fun z => x⁻¹ * z) ⁻¹' (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))),
      hKopen.preimage (continuous_const.mul continuous_id), by simp, fun b hb => ?_⟩
    have hxb : (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) = b := QuotientGroup.eq.2 hb
    simp only [hχ, hxb]
  set r : (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) → GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    fun q => q.out with hr
  set Φ : AdelicGL2 (𝓞 F) F → (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) →
      GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
    fun x q a => Ψ (x * archLift F a * finLift F (r q)) * fa a with hΦ
  have hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)), k ∈ Kf →
      Ψ (g * finLift F k) = Ψ g :=
    fun g k hk => hΨN g (finLift F k) (finLift_mem_levelOne_inf F hk)

  have hP1 : ∀ x y : AdelicGL2 (𝓞 F) F, Ψ (x * y) * f y =
      ∑ q ∈ Q, Φ x q (AdelicLevel.glArch (𝓞 F) F y) *
        (ff (AdelicLevel.glFin (𝓞 F) F y) * χ q (AdelicLevel.glFin (𝓞 F) F y)) := by
    intro x y
    by_cases hy : ff (AdelicLevel.glFin (𝓞 F) F y) = 0
    · simp [hf, hy]
    · have hq := hcover _ hy
      rw [Finset.sum_eq_single_of_mem _ hq]
      · have hχ1 : χ (AdelicLevel.glFin (𝓞 F) F y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf)
            (AdelicLevel.glFin (𝓞 F) F y) = 1 := if_pos rfl
        rw [hχ1, mul_one]
        obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Kf (AdelicLevel.glFin (𝓞 F) F y)
        have hrq : r (AdelicLevel.glFin (𝓞 F) F y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf)
            = AdelicLevel.glFin (𝓞 F) F y * k := hk
        simp only [hΦ, hf]
        rw [hrq, map_mul]
        simp only [mul_assoc]
        rw [show x * (archLift F (AdelicLevel.glArch (𝓞 F) F y) * (finLift F (AdelicLevel.glFin (𝓞 F) F y) * finLift F ↑k))
            = x * y * finLift F ↑k from by
              conv_rhs => rw [← archLift_mul_finLift F y]
              simp only [mul_assoc]]
        rw [hinv _ _ k.2]
      · intro q _ hne
        have h0 : χ q (AdelicLevel.glFin (𝓞 F) F y) = 0 := if_neg fun h => hne h.symm
        rw [h0, mul_zero, mul_zero]

  have hP2 : ∀ (x : AdelicGL2 (𝓞 F) F) (q : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf) (y : AdelicGL2 (𝓞 F) F),
      Ψ (x * finLift F (r q) * y) * f₀ y = Φ x q (AdelicLevel.glArch (𝓞 F) F y) *
        Set.indicator (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F y) := by
    intro x q y
    simp only [hf₀, hΦ]
    by_cases hy : AdelicLevel.glFin (𝓞 F) F y ∈ (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    · rw [Set.indicator_of_mem hy, mul_one, mul_one]
      have hy' : x * finLift F (r q) * y =
          x * archLift F (AdelicLevel.glArch (𝓞 F) F y) * finLift F (r q) * finLift F (AdelicLevel.glFin (𝓞 F) F y) := by
        conv_lhs => rw [← archLift_mul_finLift F y]
        simp only [← mul_assoc]
        rw [mul_assoc x (finLift F (r q)), ← archLift_mul_finLift_comm, ← mul_assoc]
      rw [hy', hinv _ _ hy]
    · rw [Set.indicator_of_notMem hy]
      simp

  have hΨcont : ∀ (x : AdelicGL2 (𝓞 F) F) (q : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf),
      Continuous fun y : AdelicGL2 (𝓞 F) F => Ψ (x * archLift F (AdelicLevel.glArch (𝓞 F) F y) * finLift F (r q)) := by
    intro x q
    refine hΨ.comp ?_
    exact (continuous_const.mul ((continuous_archLift F).comp (AdelicLevel.continuous_glArch (𝓞 F) F))).mul
      continuous_const
  have hint : ∀ (x : AdelicGL2 (𝓞 F) F) (q : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf),
      Integrable (fun y => Φ x q (AdelicLevel.glArch (𝓞 F) F y) *
        (ff (AdelicLevel.glFin (𝓞 F) F y) * χ q (AdelicLevel.glFin (𝓞 F) F y))) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro x q
    have hT : IsFactorizableTestFn F (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) *
        (ff (AdelicLevel.glFin (𝓞 F) F y) * χ q (AdelicLevel.glFin (𝓞 F) F y))) :=
      ⟨fa, fun b => ff b * χ q b, hfa, ⟨hff.1.mul (hχ_lc q), hff.2.mul_right⟩, fun _ => rfl⟩
    obtain ⟨hTc, hTs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ hT
    have heq : (fun y => Φ x q (AdelicLevel.glArch (𝓞 F) F y) *
        (ff (AdelicLevel.glFin (𝓞 F) F y) * χ q (AdelicLevel.glFin (𝓞 F) F y))) =
        fun y => Ψ (x * archLift F (AdelicLevel.glArch (𝓞 F) F y) * finLift F (r q)) *
          (fa (AdelicLevel.glArch (𝓞 F) F y) * (ff (AdelicLevel.glFin (𝓞 F) F y) * χ q (AdelicLevel.glFin (𝓞 F) F y))) := by
      funext y; simp only [hΦ]; ring
    rw [heq]
    exact ((hΨcont x q).mul hTc).integrable_of_hasCompactSupport hTs.mul_left

  have hconv : ∀ x, rightConv F Ψ f x =
      ∑ q ∈ Q, (c : ℂ) * ((∫ a, Φ x q a ∂μa) * ∫ b, ff b * χ q b ∂μf) := by
    intro x
    rw [rightConv_apply]
    simp_rw [hP1 x]
    rw [integral_finsetSum _ fun q _ => hint x q]
    exact Finset.sum_congr rfl fun q _ => hsplit (Φ x q) fun b => ff b * χ q b
  have hconv₀ : ∀ (x : AdelicGL2 (𝓞 F) F) (q : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ Kf),
      rightConv F Ψ f₀ (x * finLift F (r q)) = (c : ℂ) * ((∫ a, Φ x q a ∂μa) *
        ∫ b, Set.indicator (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) (fun _ => (1 : ℂ)) b ∂μf) := by
    intro x q
    rw [rightConv_apply]
    simp_rw [hP2 x q]
    exact hsplit (Φ x q) _

  have hVeq : ∫ b, Set.indicator (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) (fun _ => (1 : ℂ)) b ∂μf
      = ((μf Kf).toReal : ℂ) := by
    rw [integral_indicator_const (1 : ℂ) hKclosed.measurableSet, Complex.real_smul, mul_one]
    rfl
  have hV : ((μf Kf).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, ENNReal.toReal_ne_zero]
    exact ⟨hKopen.measure_ne_zero μf ⟨1, Kf.one_mem⟩, hKcomp.measure_lt_top.ne⟩
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'

  have key : rightConv F Ψ f = ∑ q ∈ Q,
      ((∫ b, ff b * χ q b ∂μf) / ((μf Kf).toReal : ℂ)) • rightTranslate F (finLift F (r q)) (rightConv F Ψ f₀) := by
    funext x
    rw [hconv x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.smul_apply, rightTranslate_apply, hconv₀ x q, hVeq, smul_eq_mul]
    symm
    rw [div_mul_eq_mul_div, div_eq_iff hV]
    ring
  rw [key]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨finLift F (r q), finLift_mem_finiteAdelicGL2Subgroup F _, rfl⟩

end S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule (solution)
