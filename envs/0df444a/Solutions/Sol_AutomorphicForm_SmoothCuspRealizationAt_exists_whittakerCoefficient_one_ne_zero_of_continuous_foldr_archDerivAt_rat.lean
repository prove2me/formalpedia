-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/323f322b-9685-5e7f-bea6-b6ed24adf634

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.StandardAddChar

noncomputable section

namespace WNVChi

abbrev hw : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace

theorem glInf_ext {x y : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ Rat.infinitePlace x = archComponent ℚ Rat.infinitePlace y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  funext v
  have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
  subst hv
  have := congrArg (fun m : GL (Fin 2) (Rat.infinitePlace).Completion =>
    (m : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion) i j) h
  exact this

theorem glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt hw m) =
      archGLIncl ℚ Rat.infinitePlace (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl ℚ _

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glArch_archRealGLAt_archRealProjAt (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = glArch (𝓞 ℚ) ℚ g := by
  apply glInf_ext
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]
  ext i j
  rw [glEquivOfRingEquiv_apply_entry]
  show (ringEquivRealOfIsReal hw).symm
      ((ringEquivRealOfIsReal hw)
        ((archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) : Matrix (Fin 2) (Fin 2) _) i j)) = _
  exact (ringEquivRealOfIsReal hw).symm_apply_apply _

theorem exists_decomp (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ k : AdelicGL2 (𝓞 ℚ) ℚ, glArch (𝓞 ℚ) ℚ k = 1 ∧ g = archRealGLAt hw (archRealProjAt hw g) * k :=
  ⟨(archRealGLAt hw (archRealProjAt hw g))⁻¹ * g, by
    rw [map_mul, map_inv, glArch_archRealGLAt_archRealProjAt, inv_mul_cancel], by
    rw [mul_inv_cancel_left]⟩

theorem unipotent_ratArchLine_eq (t : ℝ) :
    (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) : AdelicGL2 (𝓞 ℚ) ℚ) =
      archRealGLAt hw (unipotentGL2 t) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · apply glInf_ext
    rw [glArch_archRealGLAt, archComponent_archGLIncl_self]
    ext i j
    rw [glEquivOfRingEquiv_apply_entry, archComponent_apply]
    show (adeleArch (𝓞 ℚ) ℚ) (((unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) :
        GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) Rat.infinitePlace =
      (ringEquivRealOfIsReal hw).symm (((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
    rw [adeleArch_apply]
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> rfl
  · rw [glFin_archRealGLAt]
    apply Units.ext
    apply Matrix.ext
    intro i j
    show (adeleFin (𝓞 ℚ) ℚ) (((unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) :
        GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
    rw [adeleFin_apply]
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> rfl

theorem contDiff_conj_unipotent_entry (r : GL (Fin 2) ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ((r⁻¹ * unipotentGL2 t * r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  have hform : ∀ t : ℝ, ((r⁻¹ * unipotentGL2 t * r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ∑ b : Fin 2, ∑ a : Fin 2, ((r⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i a *
        (!![(1 : ℝ), t; 0, 1] a b) * ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) b j := by
    intro t
    rw [Units.val_mul, Units.val_mul, unipotentGL2_coe, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  simp_rw [hform]
  refine ContDiff.sum fun b _ => ContDiff.sum fun a _ => ?_
  refine (contDiff_const.mul ?_).mul contDiff_const
  fin_cases a <;> fin_cases b <;> simp <;> first | exact contDiff_const | exact contDiff_id

theorem contDiff_unipotent_slice {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ 2 (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)) := by
  obtain ⟨k, hk, hg⟩ := exists_decomp g
  set r : GL (Fin 2) ℝ := archRealProjAt hw g with hr

  let c : ℝ → (Fin 2 → Fin 2 → ℝ) := fun t i j =>
    ((r⁻¹ * unipotentGL2 t * r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
  have hc_of : ∀ t, Matrix.of (c t) = ((r⁻¹ * unipotentGL2 t * r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
    fun t => rfl
  have hc_det : ∀ t, (Matrix.of (c t)).det ≠ 0 := by
    intro t
    rw [hc_of, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hc_smooth : ContDiff ℝ (⊤ : ℕ∞) c :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_conj_unipotent_entry r i j
  have hmk : ∀ t, Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of (c t)) (hc_det t) =
      r⁻¹ * unipotentGL2 t * r := fun t => Units.ext rfl

  have hfun : (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)) =
      (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e)) ∘ c := by
    funext t
    simp only [Function.comp_apply]
    rw [archRealLiftAt_of_det_ne_zero hw (hc_det t), hmk, unipotent_ratArchLine_eq]
    congr 1
    rw [hg, map_mul, map_mul, map_inv]
    have hcomm := archRealGLAt_mul_comm_of_glArch_eq_one hw
      ((archRealProjAt hw g)⁻¹ * unipotentGL2 t * archRealProjAt hw g) hk
    rw [map_mul, map_mul, map_inv] at hcomm
    calc archRealGLAt hw (unipotentGL2 t) * (archRealGLAt hw (archRealProjAt hw g) * k)
        = archRealGLAt hw (archRealProjAt hw g) *
            ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * archRealGLAt hw (unipotentGL2 t) *
              archRealGLAt hw (archRealProjAt hw g) * k) := by group
      _ = archRealGLAt hw (archRealProjAt hw g) *
            (k * ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * archRealGLAt hw (unipotentGL2 t) *
              archRealGLAt hw (archRealProjAt hw g))) := by rw [hcomm]
      _ = archRealGLAt hw (archRealProjAt hw g) * k *
            ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * archRealGLAt hw (unipotentGL2 t) *
              archRealGLAt hw (archRealProjAt hw g)) := by group
  rw [hfun]
  have h := (hsm g).comp_contDiff hc_smooth fun t => hc_det t
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)

theorem continuous_unipotentGL2_adele :
    Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => (unipotentGL2 x : AdelicGL2 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
        (((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = !![1, -x; 0, 1] :=
      fun x => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem globalPoints_unipotentGL2 (β : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) := by
  apply Units.ext
  ext i j
  show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (((unipotentGL2 β : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

end WNVChi

end

open WNVChi IsDedekindDomain _root_.NumberField _root_.NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse NumberField.StandardAddChar in

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Θ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ R)
    (hsm : IsArchSmoothAt Rat.isReal_infinitePlace R.toFun)
    (hreg : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt Rat.isReal_infinitePlace) R.toFun)) :
    ∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) (NumberField.StandardAddChar.stdAddChar ℚ) R.toFun 1 g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have hψ : IsGlobalAddChar ℚ (stdAddChar ℚ) := isGlobalAddChar_stdAddChar ℚ
  letI := (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
    (adelicBox ℚ)).mS
  letI : MeasureTheory.MeasureSpace (AdelicGL2 (𝓞 ℚ) ℚ) :=
    ⟨(productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
      (adelicBox ℚ)).μ⟩
  have hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R.toFun (globalPoints (𝓞 ℚ) ℚ γ * g) = R.toFun g :=
    R.smoothCusp.1.1.1.left_invariant
  have hleftβ : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R.toFun (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = R.toFun g := by
    intro β g
    rw [← globalPoints_unipotentGL2]
    exact hleft _ g
  have hcusp : whittakerCoefficient ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) (stdAddChar ℚ) R.toFun 0 g₀ = 0 := by
    rw [whittakerCoefficient_zero_eq_constantTerm]
    exact R.smoothCusp.1.2 g₀
  have hcont : Continuous (fun x => R.toFun (unipotentGL2 x * g₀)) :=
    hR.comp (continuous_unipotentGL2_adele.mul continuous_const)
  have hsum := (AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (stdAddChar ℚ) hψ
    R.toFun hleftβ R.smoothCusp.2 (fun g => contDiff_unipotent_slice hsm g)).2 g₀
  exact AutomorphicForm.exists_whittakerCoefficient_one_ne_zero ℚ D
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (stdAddChar ℚ) hψ
    R.toFun hleft g₀ hcusp hcont hsum hg₀

end S_AutomorphicForm_SmoothCuspRealizationAt_exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat (solution)
