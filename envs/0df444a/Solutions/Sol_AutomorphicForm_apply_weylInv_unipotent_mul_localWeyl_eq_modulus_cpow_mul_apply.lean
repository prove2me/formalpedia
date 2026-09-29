-- Prove2me | solution 1 for AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9f61817b-208b-5139-ae22-45fc73915e97

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped NNReal

noncomputable section

namespace BRUHATW

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem gl_ext {g h : AdelicGL2 (𝓞 F) F} (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ u, finComponent (𝓞 F) F u (glFin (𝓞 F) F g) = finComponent (𝓞 F) F u (glFin (𝓞 F) F h)) :
    g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) h₁) i) j
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun u => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion F) => (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) (h₂ u)) i) j
    rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

theorem coe_weylInv_mul_unipotent (x : AdeleRing (𝓞 F) F) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, x] := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  have hw : ((globalPoints (𝓞 F) F gl2Weyl : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
    ext i j
    change algebraMap F (AdeleRing (𝓞 F) F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  rw [hw]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem archComponent_weylUnip (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    ((archComponent F w (glArch (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = !![0, 1; 1, x.1 w] := by
  ext i j
  rw [archComponent_apply, glArch_apply, coe_weylInv_mul_unipotent]
  fin_cases i <;> fin_cases j <;> rfl

theorem finComponent_weylUnip (x : AdeleRing (𝓞 F) F) (u : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F u (glFin (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) (u.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) = !![0, 1; 1, x.2 u] := by
  ext i j
  rw [finComponent_apply, glFin_apply, coe_weylInv_mul_unipotent]
  fin_cases i <;> fin_cases j <;> rfl

abbrev atPlace (g : GL (Fin 2) (v.adicCompletion F)) : AdelicGL2 (𝓞 F) F :=
  AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v g)

theorem glArch_atPlace (g : GL (Fin 2) (v.adicCompletion F)) : glArch (𝓞 F) F (atPlace F v g) = 1 :=
  AdelicDock.glArch_finEmbed _ _ _

theorem finComponent_atPlace_self (g : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (atPlace F v g)) = g := by
  rw [atPlace, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem finComponent_atPlace_of_ne (g : GL (Fin 2) (v.adicCompletion F)) {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) :
    finComponent (𝓞 F) F u (glFin (𝓞 F) F (atPlace F v g)) = 1 := by
  rw [atPlace, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hu]

theorem atPlace_entry (g : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    ((atPlace F v g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j)) := rfl

def beta (t : v.adicCompletion F) (ht : t ≠ 0) : GL (Fin 2) (v.adicCompletion F) :=
  ⟨!![-t⁻¹, 1; 0, t], !![-t, 1; 0, t⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]⟩

theorem coe_beta (t : v.adicCompletion F) (ht : t ≠ 0) :
    ((beta F v t ht : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![-t⁻¹, 1; 0, t] := rfl

theorem atPlace_beta_mem (t : v.adicCompletion F) (ht : t ≠ 0) : atPlace F v (beta F v t ht) ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff, atPlace_entry]
  refine Prod.ext ?_ (RestrictedProduct.ext _ _ fun u => ?_)
  · rfl
  · by_cases hu : u = v
    · subst hu
      change AdelicDock.splice (𝓞 F) F u _ _ u = (0 : FiniteAdeleRing (𝓞 F) F) u
      rw [AdelicDock.splice_apply_self, coe_beta]; rfl
    · change AdelicDock.splice (𝓞 F) F v _ _ u = (0 : FiniteAdeleRing (𝓞 F) F) u
      rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply_ne (by decide)]

def spl (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)

theorem spl_fst (x : AdeleRing (𝓞 F) F) : (spl F v x).1 = x.1 := rfl
theorem spl_snd_self (x : AdeleRing (𝓞 F) F) : (spl F v x).2 v = (x.2 v)⁻¹ := AdelicDock.splice_apply_self _ _ _ _ _
theorem spl_snd_of_ne (x : AdeleRing (𝓞 F) F) {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) : (spl F v x).2 u = x.2 u :=
  AdelicDock.splice_apply_of_ne _ _ _ _ _ hu

theorem bruhat (x : AdeleRing (𝓞 F) F) (hx : x.2 v ≠ 0) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * atPlace F v gl2Weyl =
      atPlace F v (beta F v (x.2 v) hx) *
        ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (spl F v x)) := by
  set A : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hA
  set A' : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (spl F v x) with hA'
  refine gl_ext F ?_ fun u => ?_
  · simp only [map_mul, glArch_atPlace, mul_one, one_mul]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hA, hA', glArch_apply, glArch_apply, coe_weylInv_mul_unipotent, coe_weylInv_mul_unipotent]
    fin_cases i <;> fin_cases j <;> rfl
  · simp only [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [finComponent_atPlace_self, finComponent_atPlace_self]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hA, hA', finComponent_weylUnip, finComponent_weylUnip, coe_beta, gl2Weyl_val,
        spl_snd_self]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
    · rw [finComponent_atPlace_of_ne F v _ hu, finComponent_atPlace_of_ne F v _ hu, mul_one, one_mul]
      refine Units.ext ?_
      rw [hA, hA', finComponent_weylUnip, finComponent_weylUnip, spl_snd_of_ne F v x hu]

theorem distribHaarChar_borelDiagFst_beta (t : v.adicCompletion F) (ht : t ≠ 0) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨atPlace F v (beta F v t ht), atPlace_beta_mem F v t ht⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t‖⁻¹ := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagFst_apply_val]
  change (∏ w : InfinitePlace F, ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 w‖ ^ w.mult) *
    ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 u‖ = _
  rw [atPlace_entry]
  have h1 : ∀ w : InfinitePlace F, ‖((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0) w‖ ^ w.mult = 1 := fun w => by
    rw [Matrix.one_apply_eq]; change ‖(1 : w.Completion)‖ ^ w.mult = 1; rw [norm_one, one_pow]
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  rw [finprod_eq_single _ v fun u hu => ?_]
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) _) v‖ = _
    rw [AdelicDock.splice_apply_self, coe_beta]
    simp
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) _) u‖ = 1
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply_eq]
    change ‖(1 : u.adicCompletion F)‖ = 1
    exact norm_one

theorem distribHaarChar_borelDiagSnd_beta (t : v.adicCompletion F) (ht : t ≠ 0) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨atPlace F v (beta F v t ht), atPlace_beta_mem F v t ht⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t‖ := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagSnd_apply_val]
  change (∏ w : InfinitePlace F, ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ ^ w.mult) *
    ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 u‖ = _
  rw [atPlace_entry]
  have h1 : ∀ w : InfinitePlace F, ‖((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1) w‖ ^ w.mult = 1 := fun w => by
    rw [Matrix.one_apply_eq]; change ‖(1 : w.Completion)‖ ^ w.mult = 1; rw [norm_one, one_pow]
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  rw [finprod_eq_single _ v fun u hu => ?_]
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) _) v‖ = _
    rw [AdelicDock.splice_apply_self, coe_beta]
    simp
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) _) u‖ = 1
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply_eq]
    change ‖(1 : u.adicCompletion F)‖ = 1
    exact norm_one

theorem cpow_scalar {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) * ((r : ℝ) : ℂ) ^ (-(s + 1 / 2)) = ((r : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ hr0]
  congr 1; ring

theorem main (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) t : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (x : AdeleRing (𝓞 F) F) (hx : x.2 v ≠ 0) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * atPlace F v gl2Weyl)
      = (((LanglandsTunnell.TateLocal.modulus (x.2 v) : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (spl F v x)) := by
  rw [bruhat F v x hx, hφ _ (atPlace_beta_mem F v (x.2 v) hx)]
  congr 1
  have e1 : ((etaFst 1 α hα s (borelDiagFst (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℂˣ) : ℂ) =
      ((((α (borelDiagFst (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
    rw [etaFst, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  have e2 : ((etaSnd 1 α hα s (borelDiagSnd (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℂˣ) : ℂ) =
      ((((α (borelDiagSnd (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
    rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  rw [e1, e2, hαv, hαv, distribHaarChar_borelDiagFst_beta, distribHaarChar_borelDiagSnd_beta,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  exact cpow_scalar (norm_pos_iff.mpr hx) s

end BRUHATW

end

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) (_hx : x.2 v ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x
          * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
      = (((LanglandsTunnell.TateLocal.modulus (x.2 v) : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by
  intro α hα s φ hφ v x hx
  exact BRUHATW.main F v α hα (fun t => rfl) s φ hφ x hx

end S_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
end P2MW
export P2MW.S_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply (solution)
