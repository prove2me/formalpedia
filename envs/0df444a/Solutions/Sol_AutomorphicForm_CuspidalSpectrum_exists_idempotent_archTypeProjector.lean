-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d51f90d5-8cf9-5dca-aaa9-2568befd5d1f

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous
import Theorems.Thm_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
import Theorems.Thm_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Theorems.Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 480000

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace ParchProof

section Incl

variable (F : Type) [Field F] [NumberField F]

abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion

abbrev Kprod : Type := ∀ w : InfinitePlace F, Kw F w

omit [NumberField F] in
theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w)
    (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F) (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

variable {F}

theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

theorem adelicArchGLIncl_inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    adelicArchGLIncl F (inclArch F (Pi.mulSingle w k)) = rowIsometryInclAt₀ F w k := by
  rw [inclArch_mulSingle]; rfl

theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

theorem continuous_inclArch : Continuous (inclArch F) := by
  have hval : Continuous fun κ : Kprod F =>
      ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => ?_
    refine continuous_pi fun w => ?_
    simp only [inclArch_entry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) := by
  classical
  have h : (rowIsometryInclAt₀ F w : Kw F w → AdelicGL2 (𝓞 F) F)
      = fun k => adelicArchGLIncl F (inclArch F (Pi.mulSingle w k)) :=
    funext fun k => (adelicArchGLIncl_inclArch_mulSingle w k).symm
  rw [h]
  exact continuous_adelicArchGLIncl.comp (continuous_inclArch.comp (continuous_mulSingle w))

theorem injective_rowIsometryInclAt₀ (w : InfinitePlace F) : Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a b hab
  have h : archComponent F w (glArch (𝓞 F) F (rowIsometryInclAt₀ F w a))
      = archComponent F w (glArch (𝓞 F) F (rowIsometryInclAt₀ F w b)) := by rw [hab]
  rw [glArch_rowIsometryInclAt₀, glArch_rowIsometryInclAt₀] at h
  unfold archRowIsometryInclAt₀ at h
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, archComponent_archGLIncl_self,
    archComponent_archGLIncl_self] at h
  exact Subtype.ext h

theorem commute_of_glArch_eq_one_of_glFin_eq_one {g y : AdelicGL2 (𝓞 F) F}
    (hg : glArch (𝓞 F) F g = 1) (hy : glFin (𝓞 F) F y = 1) : Commute g y := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have h1 := AdelicLevel.glArch_apply (R := 𝓞 F) (K := F) (g * y) i j
    have h2 := AdelicLevel.glArch_apply (R := 𝓞 F) (K := F) (y * g) i j
    show ((((g * y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1)
      = ((((y * g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1)
    rw [← h1, ← h2, map_mul, map_mul, hg, one_mul, mul_one]
  · have h1 := AdelicLevel.glFin_apply (R := 𝓞 F) (K := F) (g * y) i j
    have h2 := AdelicLevel.glFin_apply (R := 𝓞 F) (K := F) (y * g) i j
    show ((((g * y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2)
      = ((((y * g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2)
    rw [← h1, ← h2, map_mul, map_mul, hy, one_mul, mul_one]

theorem commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ finiteAdelicGL2Subgroup F) (w : InfinitePlace F) (k : Kw F w) :
    Commute g (rowIsometryInclAt₀ F w k) :=
  commute_of_glArch_eq_one_of_glFin_eq_one hg (glFin_rowIsometryInclAt₀ F w k)

end Incl

section Dense

variable (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
  (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

scoped instance completeSpace_cuspSubcarrier : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem exists_mem_norm_sub_lt (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ < ε := by
  have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
    rw [← Submodule.topologicalClosure_coe]; exact v.2
  obtain ⟨a, haA, hav⟩ := Metric.mem_closure_iff.mp hv ε hε
  obtain ⟨φm, hφm, rfl⟩ := haA
  refine ⟨φm, hφm, ?_⟩
  rw [Submodule.coe_norm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, ← dist_eq_norm]
  exact hav

variable {F hΦ₀ σ ξ}

theorem eq_of_isCuspLift {op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)}
    (hop : ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, op φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    {S S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (hS : IsCuspLift F hΦ₀ σ ξ op S) (hS' : IsCuspLift F hΦ₀ σ ξ op S') : S = S' := by
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  refine ContinuousLinearMap.ext fun v => ?_

  have key : ∀ ε : ℝ, 0 < ε → ‖S v - S' v‖ ≤ (‖S‖ + ‖S'‖) * ε := by
    intro ε hε
    obtain ⟨φ, hφ, hva⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ v ε hε
    have hSa : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = S' (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) := by
      rw [hS ⟨φ, hφ⟩ (hop φ hφ), hS' ⟨φ, hφ⟩ (hop φ hφ)]
    have hdec : S v - S' v = S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) - S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) := by
      rw [map_sub, map_sub, hSa]; abel
    rw [hdec]
    calc ‖S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) - S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖
        ≤ ‖S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ + ‖S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ := norm_sub_le _ _
      _ ≤ ‖S‖ * ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ + ‖S'‖ * ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ :=
          add_le_add (S.le_opNorm _) (S'.le_opNorm _)
      _ ≤ ‖S‖ * ε + ‖S'‖ * ε := add_le_add (mul_le_mul_of_nonneg_left hva.le (norm_nonneg S))
          (mul_le_mul_of_nonneg_left hva.le (norm_nonneg S'))
      _ = (‖S‖ + ‖S'‖) * ε := by ring
  have h0 : ‖S v - S' v‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have hpos : 0 < ‖S‖ + ‖S'‖ + 1 := by positivity
    have := key (‖S v - S' v‖ / (2 * (‖S‖ + ‖S'‖ + 1))) (by positivity)
    have hlt : (‖S‖ + ‖S'‖) * (‖S v - S' v‖ / (2 * (‖S‖ + ‖S'‖ + 1))) < ‖S v - S' v‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg S, norm_nonneg S']
    exact absurd (this.trans_lt hlt) (lt_irrefl _)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

namespace IsCuspLift

private theorem _root_.ParchProof.IsCuspLift.comp {op₁ op₂ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)}
    (hop₁ : ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, op₁ φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    {S₁ S₂ : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (hS₁ : IsCuspLift F hΦ₀ σ ξ op₁ S₁) (hS₂ : IsCuspLift F hΦ₀ σ ξ op₂ S₂) :
    IsCuspLift F hΦ₀ σ ξ (fun φ => op₂ (op₁ φ)) (S₂.comp S₁) := by
  intro φ h
  rw [ContinuousLinearMap.comp_apply, hS₁ φ (hop₁ φ φ.2), hS₂ ⟨op₁ φ, hop₁ φ φ.2⟩ h]

end IsCuspLift
p2m_export "ParchProof" "IsCuspLift.comp"
include hΦ₀ in

theorem rightTranslate_mem (y : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) : rightTranslate F y φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
  AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ y φ hφ

theorem comp_eq_comp_of_isCuspLift_rightTranslate {g y : AdelicGL2 (𝓞 F) F} (hgy : Commute g y)
    {S T : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (hS : IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S) (hT : IsCuspLift F hΦ₀ σ ξ (rightTranslate F y) T) :
    S.comp T = T.comp S := by
  have h1 : IsCuspLift F hΦ₀ σ ξ (fun φ => rightTranslate F g (rightTranslate F y φ)) (S.comp T) :=
    IsCuspLift.comp (rightTranslate_mem (hΦ₀ := hΦ₀) y) hT hS
  have h2 : IsCuspLift F hΦ₀ σ ξ (fun φ => rightTranslate F y (rightTranslate F g φ)) (T.comp S) :=
    IsCuspLift.comp (rightTranslate_mem (hΦ₀ := hΦ₀) g) hS hT
  have hop : (fun φ : AdelicGL2 (𝓞 F) F → ℂ => rightTranslate F y (rightTranslate F g φ))
      = fun φ => rightTranslate F g (rightTranslate F y φ) := by
    funext φ
    rw [rightTranslate_rightTranslate, rightTranslate_rightTranslate, hgy.eq]
  rw [hop] at h2
  refine eq_of_isCuspLift (fun φ hφ => ?_) h1 h2
  exact rightTranslate_mem (hΦ₀ := hΦ₀) g _ (rightTranslate_mem (hΦ₀ := hΦ₀) y φ hφ)

end Dense

section Lists

variable {ι M : Type*} [Monoid M] (f : ι → M)

theorem mul_listProd_of_mem (hidem : ∀ i, f i * f i = f i) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∀ (l : List ι) (i : ι), i ∈ l → f i * (l.map f).prod = (l.map f).prod
  | [], i, hi => absurd hi (List.not_mem_nil)
  | (a :: t), i, hi => by
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hi with rfl | hit
    · rw [← mul_assoc, hidem]
    · rw [← mul_assoc, (hcomm i a).eq, mul_assoc, mul_listProd_of_mem hidem hcomm t i hit]

theorem listProd_mul_listProd_of_subset (hidem : ∀ i, f i * f i = f i) (hcomm : ∀ i j, Commute (f i) (f j))
    (l : List ι) : ∀ l' : List ι, (∀ i ∈ l', i ∈ l) → (l'.map f).prod * (l.map f).prod = (l.map f).prod
  | [], _ => by rw [List.map_nil, List.prod_nil, one_mul]
  | (a :: t), h => by
    rw [List.map_cons, List.prod_cons, mul_assoc,
      listProd_mul_listProd_of_subset hidem hcomm l t (fun i hi => h i (List.mem_cons_of_mem a hi)),
      mul_listProd_of_mem f hidem hcomm l a (h a List.mem_cons_self)]

theorem listProd_mul_self (hidem : ∀ i, f i * f i = f i) (hcomm : ∀ i j, Commute (f i) (f j)) (l : List ι) :
    (l.map f).prod * (l.map f).prod = (l.map f).prod :=
  listProd_mul_listProd_of_subset f hidem hcomm l l fun _ h => h

theorem commute_listProd {T : M} (h : ∀ i, Commute T (f i)) (l : List ι) : Commute T (l.map f).prod :=
  Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact h i

theorem listProd_eq_mul_of_mem [DecidableEq ι] (hcomm : ∀ i j, Commute (f i) (f j)) (l : List ι) (i : ι)
    (hi : i ∈ l) : (l.map f).prod = f i * ((l.erase i).map f).prod := by
  have hp : (l.map f).Perm ((i :: l.erase i).map f) := (List.perm_cons_erase hi).map f
  rw [hp.prod_eq' ?_, List.map_cons, List.prod_cons]
  exact (List.pairwise_of_forall (l := l) fun a b => hcomm a b).map f fun _ _ h => h

variable {H : Type*} [TopologicalSpace H] [AddCommMonoid H] [Module ℂ H] (A : ι → (H →L[ℂ] H))

theorem listProd_apply_eq_self {v : H} (h : ∀ i, A i v = v) : ∀ l : List ι, (l.map A).prod v = v
  | [] => by rw [List.map_nil, List.prod_nil, ContinuousLinearMap.one_apply]
  | (a :: t) => by rw [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply, listProd_apply_eq_self h t, h a]

theorem listProd_apply_mem (p : Submodule ℂ H) (h : ∀ i, ∀ x ∈ p, A i x ∈ p) :
    ∀ (l : List ι), ∀ x ∈ p, (l.map A).prod x ∈ p
  | [], x, hx => by rwa [List.map_nil, List.prod_nil, ContinuousLinearMap.one_apply]
  | (a :: t), x, hx => by
    rw [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    exact h a _ (listProd_apply_mem p h t x hx)

end Lists

section Infra

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

scoped instance compactSpace_Kw (w : InfinitePlace F) : CompactSpace (Kw F w) :=
  isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)

scoped instance measurableSpace_Kw (w : InfinitePlace F) : MeasurableSpace (Kw F w) := borel _

scoped instance borelSpace_Kw (w : InfinitePlace F) : BorelSpace (Kw F w) := ⟨rfl⟩

def μw (w : InfinitePlace F) : Measure (Kw F w) := Measure.haarMeasure ⊤

scoped instance isHaarMeasure_μw (w : InfinitePlace F) : (μw F w).IsHaarMeasure := by
  unfold μw; infer_instance

scoped instance isProbabilityMeasure_μw (w : InfinitePlace F) : IsProbabilityMeasure (μw F w) :=
  ⟨by rw [μw, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
  (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
  (hσ : HasModulus F ξ σ)

include hσ in
theorem sir : ∃ π : Kprod F →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
    (∀ κ : Kprod F, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (adelicArchGLIncl F (inclArch F κ))) (π κ)) ∧
    (∀ (κ : Kprod F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π κ v‖ = ‖v‖) ∧
    (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun κ : Kprod F => π κ v) :=
  AutomorphicForm.CuspidalSpectrum.exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous
    F hΦ₀ σ ξ hσ (inclArch F) archComponent_inclArch

include hσ in

def piK : Kprod F →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
  (sir F hΦ₀ σ ξ hσ).choose

theorem isCuspLift_piK (κ : Kprod F) :
    IsCuspLift F hΦ₀ σ ξ (rightTranslate F (adelicArchGLIncl F (inclArch F κ))) (piK F hΦ₀ σ ξ hσ κ) :=
  (sir F hΦ₀ σ ξ hσ).choose_spec.1 κ

theorem norm_piK_apply (κ : Kprod F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : ‖piK F hΦ₀ σ ξ hσ κ v‖ = ‖v‖ :=
  (sir F hΦ₀ σ ξ hσ).choose_spec.2.1 κ v

theorem continuous_piK_apply (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Continuous fun κ : Kprod F => piK F hΦ₀ σ ξ hσ κ v :=
  (sir F hΦ₀ σ ξ hσ).choose_spec.2.2 v

theorem piK_apply_toCuspSubcarrier (κ : Kprod F) (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) :
    piK F hΦ₀ σ ξ hσ κ (toCuspSubcarrier F hΦ₀ σ ξ φ)
      = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (adelicArchGLIncl F (inclArch F κ)) φ,
          rightTranslate_mem (hΦ₀ := hΦ₀) _ _ φ.2⟩ :=
  isCuspLift_piK F hΦ₀ σ ξ hσ κ φ _

include hσ in

def Sw (w : InfinitePlace F) : Kw F w →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
  (piK F hΦ₀ σ ξ hσ).comp (MonoidHom.mulSingle (fun v : InfinitePlace F => Kw F v) w)

theorem Sw_apply (w : InfinitePlace F) (k : Kw F w) :
    Sw F hΦ₀ σ ξ hσ w k = piK F hΦ₀ σ ξ hσ (Pi.mulSingle w k) := rfl

theorem isCuspLift_Sw (w : InfinitePlace F) (k : Kw F w) :
    IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) (Sw F hΦ₀ σ ξ hσ w k) := by
  have h := isCuspLift_piK F hΦ₀ σ ξ hσ (Pi.mulSingle w k)
  rwa [adelicArchGLIncl_inclArch_mulSingle] at h

theorem Sw_apply_toCuspSubcarrier (w : InfinitePlace F) (k : Kw F w) (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) :
    Sw F hΦ₀ σ ξ hσ w k (toCuspSubcarrier F hΦ₀ σ ξ φ)
      = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) φ,
          rightTranslate_mem (hΦ₀ := hΦ₀) _ _ φ.2⟩ :=
  isCuspLift_Sw F hΦ₀ σ ξ hσ w k φ _

theorem norm_Sw_apply (w : InfinitePlace F) (k : Kw F w) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    ‖Sw F hΦ₀ σ ξ hσ w k v‖ = ‖v‖ :=
  norm_piK_apply F hΦ₀ σ ξ hσ _ v

theorem norm_Sw_le (w : InfinitePlace F) (k : Kw F w) : ‖Sw F hΦ₀ σ ξ hσ w k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [one_mul, norm_Sw_apply]

theorem continuous_Sw_apply (w : InfinitePlace F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    Continuous fun k : Kw F w => Sw F hΦ₀ σ ξ hσ w k v :=
  (continuous_piK_apply F hΦ₀ σ ξ hσ v).comp (continuous_mulSingle w)

theorem commute_Sw_Sw {v w : InfinitePlace F} (hvw : v ≠ w) (a : Kw F v) (b : Kw F w) :
    Commute (Sw F hΦ₀ σ ξ hσ v a) (Sw F hΦ₀ σ ξ hσ w b) :=
  (Pi.mulSingle_commute hvw a b).map (piK F hΦ₀ σ ξ hσ)

variable (tys : ArchTypeFamily F)

theorem contCoeff (w : InfinitePlace F) :
    ∃ (n : ℕ) (ρc : Kw F w →* Matrix (Fin n) (Fin n) ℂ), Continuous ρc ∧
      ∀ (G : Type) [Group G] (ι : Kw F w →* G), Function.Injective ι →
        (∀ (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : Kw F w) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, typeSubmodule ι ((tys.rep w i).ρ)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι ((tys.rep w i).ρ), (∀ y : G, Continuous fun k : Kw F w => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)), T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : Kw F w => fun y : G => f (y * ι k))) :=
  AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
    (fun i : Fin (tys.card w) => (tys.rep w i).ρ)

include tys in

def nw (w : InfinitePlace F) : ℕ := (contCoeff F tys w).choose

def ρc (w : InfinitePlace F) : Kw F w →* Matrix (Fin (nw F tys w)) (Fin (nw F tys w)) ℂ :=
  (contCoeff F tys w).choose_spec.choose

theorem continuous_ρc (w : InfinitePlace F) : Continuous (ρc F tys w) :=
  (contCoeff F tys w).choose_spec.choose_spec.1

theorem ρc_spec (w : InfinitePlace F) :
    ∀ (G : Type) [Group G] (ι : Kw F w →* G), Function.Injective ι →
        (∀ (T : (Fin (nw F tys w) → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : Kw F w) (x : Fin (nw F tys w) → ℂ), T ((ρc F tys w k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin (nw F tys w) → ℂ, T x ∈ ⨆ i, typeSubmodule ι ((tys.rep w i).ρ)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι ((tys.rep w i).ρ), (∀ y : G, Continuous fun k : Kw F w => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)),
              T (fun j => (ρc F tys w k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : Kw F w => fun y : G => f (y * ι k))) :=
  (contCoeff F tys w).choose_spec.choose_spec.2

theorem charIdem (w : InfinitePlace F) :
    ∃ e : Kw F w → ℂ, Continuous e ∧ (∀ k l : Kw F w, e (l * k * l⁻¹) = e k) ∧
      (∀ k : Kw F w, e k⁻¹ = (starRingEnd ℂ) (e k)) ∧
      (∀ k : Kw F w, ∫ l, e l * e (l⁻¹ * k) ∂(μw F w) = e k) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : Kw F w →* (H →L[ℂ] H)), (∀ (k : Kw F w) (v : H), ‖π k v‖ = ‖v‖) →
        (∀ v : H, Continuous fun k : Kw F w => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂(μw F w)) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →L[ℂ] H),
              (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)), T (fun i => (ρc F tys w k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →L[ℂ] H),
              (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)), T (fun i => (ρc F tys w k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] H)) :=
  MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
    (μw F w) (ρc F tys w) (continuous_ρc F tys w)

include tys in

def ew (w : InfinitePlace F) : Kw F w → ℂ := (charIdem F tys w).choose

theorem continuous_ew (w : InfinitePlace F) : Continuous (ew F tys w) := (charIdem F tys w).choose_spec.1

theorem ew_conj (w : InfinitePlace F) (k l : Kw F w) : ew F tys w (l * k * l⁻¹) = ew F tys w k :=
  (charIdem F tys w).choose_spec.2.1 k l

theorem ew_inv (w : InfinitePlace F) (k : Kw F w) : ew F tys w k⁻¹ = (starRingEnd ℂ) (ew F tys w k) :=
  (charIdem F tys w).choose_spec.2.2.1 k

theorem ew_conv (w : InfinitePlace F) (k : Kw F w) :
    ∫ l, ew F tys w l * ew F tys w (l⁻¹ * k) ∂(μw F w) = ew F tys w k :=
  (charIdem F tys w).choose_spec.2.2.2.1 k

theorem ew_isotypic (w : InfinitePlace F) :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : Kw F w →* (H →L[ℂ] H)), (∀ (k : Kw F w) (v : H), ‖π k v‖ = ‖v‖) →
        (∀ v : H, Continuous fun k : Kw F w => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (ew F tys w k) • (π k v) ∂(μw F w)) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →L[ℂ] H),
              (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)), T (fun i => (ρc F tys w k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →L[ℂ] H),
              (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)), T (fun i => (ρc F tys w k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] H)) :=
  (charIdem F tys w).choose_spec.2.2.2.2

include hσ tys in

def avgOp (w : InfinitePlace F) :=
  ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
    (μw F w) (Sw F hΦ₀ σ ξ hσ w) 1 (norm_Sw_le F hΦ₀ σ ξ hσ w) (continuous_Sw_apply F hΦ₀ σ ξ hσ w)
    (ew F tys w) (continuous_ew F tys w)

include hσ tys in

def Ew (w : InfinitePlace F) : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  (avgOp F hΦ₀ σ ξ hσ tys w).choose

theorem Ew_apply (w : InfinitePlace F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    Ew F hΦ₀ σ ξ hσ tys w v = ∫ c, (ew F tys w c) • (Sw F hΦ₀ σ ξ hσ w c v) ∂(μw F w) :=
  (avgOp F hΦ₀ σ ξ hσ tys w).choose_spec.1 v

theorem norm_Ew_apply_le (w : InfinitePlace F) (M : ℝ) (hM : ∀ c, ‖ew F tys w c‖ ≤ M)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : ‖Ew F hΦ₀ σ ξ hσ tys w v‖ ≤ M * ‖v‖ := by
  have h := (avgOp F hΦ₀ σ ξ hσ tys w).choose_spec.2.1 M hM v
  rwa [mul_one] at h

theorem Ew_map_le (w : InfinitePlace F) (L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hL : IsClosed (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hLS : ∀ c, L.map (Sw F hΦ₀ σ ξ hσ w c : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ L) :
    L.map (Ew F hΦ₀ σ ξ hσ tys w : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ L :=
  (avgOp F hΦ₀ σ ξ hσ tys w).choose_spec.2.2.1 L hL hLS

theorem Ew_apply_mem (w : InfinitePlace F) (L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hL : IsClosed (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hLS : ∀ c, ∀ x ∈ L, Sw F hΦ₀ σ ξ hσ w c x ∈ L) : ∀ x ∈ L, Ew F hΦ₀ σ ξ hσ tys w x ∈ L := by
  intro x hx
  refine Ew_map_le F hΦ₀ σ ξ hσ tys w L hL (fun c => ?_) (Submodule.mem_map_of_mem hx)
  rintro _ ⟨y, hy, rfl⟩
  exact hLS c y hy

theorem Ew_comm (w : InfinitePlace F) (T : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hT : ∀ c, T.comp (Sw F hΦ₀ σ ξ hσ w c) = (Sw F hΦ₀ σ ξ hσ w c).comp T) :
    T.comp (Ew F hΦ₀ σ ξ hσ tys w) = (Ew F hΦ₀ σ ξ hσ tys w).comp T :=
  (avgOp F hΦ₀ σ ξ hσ tys w).choose_spec.2.2.2 T hT

theorem commute_Ew_of (w : InfinitePlace F) (T : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hT : ∀ c, Commute T (Sw F hΦ₀ σ ξ hσ w c)) : Commute T (Ew F hΦ₀ σ ξ hσ tys w) := by
  have h := Ew_comm F hΦ₀ σ ξ hσ tys w T fun c => by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]; exact (hT c).eq
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at h
  exact h

theorem Ew_charIdem (w : InfinitePlace F) :
    (Ew F hΦ₀ σ ξ hσ tys w).comp (Ew F hΦ₀ σ ξ hσ tys w) = Ew F hΦ₀ σ ξ hσ tys w ∧
    (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Ew F hΦ₀ σ ξ hσ tys w v = v ↔
      ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
        (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)),
          T (fun i => (ρc F tys w k).mulVec (x i)) = Sw F hΦ₀ σ ξ hσ w k (T x)) ∧
        v ∈ LinearMap.range (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))) ∧
    (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ∃ (m : ℕ) (T : (Fin m → (Fin (nw F tys w) → ℂ)) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
        (∀ (k : Kw F w) (x : Fin m → (Fin (nw F tys w) → ℂ)),
          T (fun i => (ρc F tys w k).mulVec (x i)) = Sw F hΦ₀ σ ξ hσ w k (T x)) ∧
        Ew F hΦ₀ σ ξ hσ tys w v ∈
          LinearMap.range (T : (Fin m → (Fin (nw F tys w) → ℂ)) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))) :=
  ew_isotypic F tys w ↥(cuspSubcarrier F hΦ₀ σ ξ) (Sw F hΦ₀ σ ξ hσ w) (norm_Sw_apply F hΦ₀ σ ξ hσ w)
    (continuous_Sw_apply F hΦ₀ σ ξ hσ w) (Ew F hΦ₀ σ ξ hσ tys w) (avgOp F hΦ₀ σ ξ hσ tys w).choose_spec.1

theorem Ew_mul_Ew (w : InfinitePlace F) :
    Ew F hΦ₀ σ ξ hσ tys w * Ew F hΦ₀ σ ξ hσ tys w = Ew F hΦ₀ σ ξ hσ tys w := by
  rw [ContinuousLinearMap.mul_def]; exact (Ew_charIdem F hΦ₀ σ ξ hσ tys w).1

theorem commute_Ew (v w : InfinitePlace F) : Commute (Ew F hΦ₀ σ ξ hσ tys v) (Ew F hΦ₀ σ ξ hσ tys w) := by
  by_cases hvw : v = w
  · subst hvw; exact Commute.refl _
  · refine commute_Ew_of F hΦ₀ σ ξ hσ tys w _ fun b => ?_
    exact (commute_Ew_of F hΦ₀ σ ξ hσ tys v _ fun a => (commute_Sw_Sw F hΦ₀ σ ξ hσ (Ne.symm hvw) b a)).symm

include hσ tys in

def E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map (Ew F hΦ₀ σ ξ hσ tys)).prod

theorem E_def : E F hΦ₀ σ ξ hσ tys
    = (((Finset.univ : Finset (InfinitePlace F)).toList).map (Ew F hΦ₀ σ ξ hσ tys)).prod := rfl

theorem E_mul_E : E F hΦ₀ σ ξ hσ tys * E F hΦ₀ σ ξ hσ tys = E F hΦ₀ σ ξ hσ tys :=
  listProd_mul_self _ (Ew_mul_Ew F hΦ₀ σ ξ hσ tys) (commute_Ew F hΦ₀ σ ξ hσ tys) _

theorem Ew_mul_E (w : InfinitePlace F) : Ew F hΦ₀ σ ξ hσ tys w * E F hΦ₀ σ ξ hσ tys = E F hΦ₀ σ ξ hσ tys :=
  mul_listProd_of_mem _ (Ew_mul_Ew F hΦ₀ σ ξ hσ tys) (commute_Ew F hΦ₀ σ ξ hσ tys) _ w
    (Finset.mem_toList.mpr (Finset.mem_univ w))

theorem Ew_apply_E_apply (w : InfinitePlace F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    Ew F hΦ₀ σ ξ hσ tys w (E F hΦ₀ σ ξ hσ tys v) = E F hΦ₀ σ ξ hσ tys v := by
  rw [← ContinuousLinearMap.mul_apply, Ew_mul_E]

theorem E_eq_Ew_mul (w : InfinitePlace F) : E F hΦ₀ σ ξ hσ tys
    = Ew F hΦ₀ σ ξ hσ tys w * ((((Finset.univ : Finset (InfinitePlace F)).toList).erase w).map (Ew F hΦ₀ σ ξ hσ tys)).prod :=
  listProd_eq_mul_of_mem _ (commute_Ew F hΦ₀ σ ξ hσ tys) _ w (Finset.mem_toList.mpr (Finset.mem_univ w))

theorem commute_E {T : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (h : ∀ w, Commute T (Ew F hΦ₀ σ ξ hσ tys w)) : Commute T (E F hΦ₀ σ ξ hσ tys) :=
  commute_listProd _ h _

theorem E_apply_eq_self {v : ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : ∀ w, Ew F hΦ₀ σ ξ hσ tys w v = v) :
    E F hΦ₀ σ ξ hσ tys v = v :=
  listProd_apply_eq_self _ h _

theorem E_apply_mem (p : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (h : ∀ w, ∀ x ∈ p, Ew F hΦ₀ σ ξ hσ tys w x ∈ p) : ∀ x ∈ p, E F hΦ₀ σ ξ hσ tys x ∈ p :=
  listProd_apply_mem _ p h _

end Infra

end ParchProof

namespace ParchProof34

variable (F : Type) [Field F] [NumberField F]

abbrev Kw (w : InfinitePlace F) : Type := ↥(rowIsometrySubgroup₀ w.Completion)

section Helpers

variable {F}

omit [NumberField F] in

theorem continuous_archGLIncl (w : InfinitePlace F) : Continuous (archGLIncl F w) := by
  have hval : ∀ m : GL (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) w.Completion, Continuous m →
      Continuous fun k => archMatrixUpdate F w (m k) := by
    intro m hm
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    by_cases hv : v = w
    · subst hv
      simp only [archMatrixUpdate_apply_self]
      exact hm.matrix_elem i j
    · simp only [archMatrixUpdate_apply_of_ne F w _ i j hv]
      exact continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hval _ Units.continuous_val
  · have : (fun k : GL (Fin 2) w.Completion => ((archGLIncl F w k)⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)).val)
        = fun k => archMatrixUpdate F w ((k⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
      funext k; rw [← map_inv]; rfl
    rw [this]
    exact hval _ (Units.continuous_val.comp continuous_inv)

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) :=
  continuous_adelicArchGLIncl.comp ((continuous_archGLIncl w).comp continuous_subtype_val)

private theorem _root_.ParchProof34.injective_rowIsometryInclAt₀ (w : InfinitePlace F) : Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a b h
  have h1 : archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w a))
      = archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w b)) := by rw [h]
  rw [glArch_rowIsometryInclAt₀, glArch_rowIsometryInclAt₀] at h1
  change archComponent F w (archGLIncl F w a) = archComponent F w (archGLIncl F w b) at h1
  rw [archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h1
  exact Subtype.ext h1

p2m_export "ParchProof34" "injective_rowIsometryInclAt₀"

theorem eq_of_glArch_eq_of_glFin_eq {g h : AdelicGL2 (𝓞 F) F}
    (ha : AdelicLevel.glArch (𝓞 F) F g = AdelicLevel.glArch (𝓞 F) F h)
    (hf : AdelicLevel.glFin (𝓞 F) F g = AdelicLevel.glFin (𝓞 F) F h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have h1 : (AdelicLevel.glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
        = (AdelicLevel.glArch (𝓞 F) F h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by rw [ha]
    rw [AdelicLevel.glArch_apply, AdelicLevel.glArch_apply] at h1
    exact h1
  · have h1 : (AdelicLevel.glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        = (AdelicLevel.glFin (𝓞 F) F h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by rw [hf]
    rw [AdelicLevel.glFin_apply, AdelicLevel.glFin_apply] at h1
    exact h1

theorem commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup (w : InfinitePlace F) (k : Kw F w)
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F) :
    Commute (rowIsometryInclAt₀ F w k) u := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hu
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hu, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀, mul_one, one_mul]

end Helpers

section Restrict

variable {G : Type*} [Monoid G] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def restrictHom (S : G →* (E →L[ℂ] E)) (W : Submodule ℂ E) (hW : ∀ (g : G) (x : ↥W), S g x ∈ W) :
    G →* (↥W →L[ℂ] ↥W) where
  toFun g := ((S g).comp W.subtypeL).codRestrict W (hW g)
  map_one' := ContinuousLinearMap.ext fun x => Subtype.ext (by
    show S 1 (x : E) = x
    rw [map_one]; rfl)
  map_mul' g h := ContinuousLinearMap.ext fun x => Subtype.ext (by
    show S (g * h) (x : E) = S g (S h (x : E))
    rw [map_mul]; rfl)

theorem restrictHom_coe (S : G →* (E →L[ℂ] E)) (W : Submodule ℂ E) (hW : ∀ (g : G) (x : ↥W), S g x ∈ W)
    (g : G) (x : ↥W) : ((restrictHom S W hW g x : ↥W) : E) = S g x := rfl

def restrictCLM (A : E →L[ℂ] E) (W : Submodule ℂ E) (hW : ∀ x : ↥W, A x ∈ W) : ↥W →L[ℂ] ↥W :=
  (A.comp W.subtypeL).codRestrict W hW

theorem restrictCLM_coe (A : E →L[ℂ] E) (W : Submodule ℂ E) (hW : ∀ x : ↥W, A x ∈ W) (x : ↥W) :
    ((restrictCLM A W hW x : ↥W) : E) = A x := rfl

end Restrict

section Clause3

variable {F}
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem apply_toCuspSubcarrier_eq_of_range_eq_span (w : InfinitePlace F)
    (S : Kw F w →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hS : ∀ k : Kw F w, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) (S k))
    {n : ℕ} (ρc : Kw F w →* Matrix (Fin n) (Fin n) ℂ)
    (A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hA : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ),
      (∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
        (∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρc k).mulVec (x i)) = S k (T x)) ∧
        v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))) → A v = v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    {m : ℕ} (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hT : ∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)),
      T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * rowIsometryInclAt₀ F w k))
    (hTr : LinearMap.range T = Submodule.span ℂ (Set.range fun k : Kw F w =>
      fun y : AdelicGL2 (𝓞 F) F => φ (y * rowIsometryInclAt₀ F w k))) :
    A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ := by

  have hVle : LinearMap.range T ≤ cuspMemberSubmodule F Φ₀ ξ := by
    rw [hTr, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (rowIsometryInclAt₀ F w k) φ hφ

  let Tm : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] ↥(cuspMemberSubmodule F Φ₀ ξ) :=
    LinearMap.codRestrict (cuspMemberSubmodule F Φ₀ ξ) T (fun x => hVle (LinearMap.mem_range_self T x))
  let Tc : (Fin m → (Fin n → ℂ)) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    LinearMap.toContinuousLinearMap ((toCuspSubcarrier F hΦ₀ σ ξ).comp Tm)
  have hTc_apply : ∀ x, Tc x = toCuspSubcarrier F hΦ₀ σ ξ ⟨T x, hVle (LinearMap.mem_range_self T x)⟩ :=
    fun x => rfl
  have hTc : ∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)), Tc (fun i => (ρc k).mulVec (x i)) = S k (Tc x) := by
    intro k x
    rw [hTc_apply, hTc_apply]
    have hmem : rightTranslate F (rowIsometryInclAt₀ F w k) (T x) ∈ cuspMemberSubmodule F Φ₀ ξ :=
      rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ _ _ (hVle (LinearMap.mem_range_self T x))
    rw [hS k ⟨T x, hVle (LinearMap.mem_range_self T x)⟩ hmem]
    congr 1
    exact Subtype.ext (hT k x)

  have hφmem : φ ∈ LinearMap.range T := by
    rw [hTr]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y
    simp
  obtain ⟨x₀, hx₀⟩ := hφmem
  refine hA _ ⟨m, Tc, hTc, x₀, ?_⟩
  show Tc x₀ = _
  rw [hTc_apply]
  congr 1
  exact Subtype.ext hx₀

end Clause3

section Clause4w

variable {F}
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem toCuspSubcarrier_injective : Function.Injective (toCuspSubcarrier F hΦ₀ σ ξ) := by
  intro a b h
  rw [← sub_eq_zero] at h ⊢
  rw [← map_sub] at h
  set c := a - b with hc
  have h0 : toCarrier F hΦ₀ σ ξ ⟨(c : AdelicGL2 (𝓞 F) F → ℂ), c.2.1.1.1⟩ = 0 := by
    rw [← toCuspSubcarrier_apply_coe, h]; rfl
  have := eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (c : AdelicGL2 (𝓞 F) F → ℂ) ⟨c.2.1.1.1, c.2.2⟩ h0
  exact Subtype.ext this

theorem mem_of_apply_toCuspSubcarrier_eq (w : InfinitePlace F)
    [MeasurableSpace (Kw F w)] [BorelSpace (Kw F w)] (μ : Measure (Kw F w))
    (S : Kw F w →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hS : ∀ k : Kw F w, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) (S k))
    (hSn : ∀ (k : Kw F w) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖S k v‖ = ‖v‖)
    (hSc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun k : Kw F w => S k v)
    {n : ℕ} (ρc : Kw F w →* Matrix (Fin n) (Fin n) ℂ) (e : Kw F w → ℂ)
    (hCI : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : Kw F w →* (H →L[ℂ] H)), (∀ (k : Kw F w) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : Kw F w => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂μ) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρc k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρc k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)))
    (P : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hK1 : ∀ (T : (Fin n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ (k : Kw F w) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * rowIsometryInclAt₀ F w k)) →
      ∀ x : Fin n → ℂ, T x ∈ P)
    (Ew : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hEw : ∀ v, Ew v = ∫ k, (e k) • (S k v) ∂μ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ ↥V]
    (hVle : V ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hVst : ∀ (k : Kw F w), ∀ v ∈ V, rightTranslate F (rowIsometryInclAt₀ F w k) v ∈ V)
    (hEwV : ∀ v (hv : v ∈ V), ∃ v' : AdelicGL2 (𝓞 F) F → ℂ, ∃ hv' : v' ∈ V,
      Ew (toCuspSubcarrier F hΦ₀ σ ξ ⟨v, hVle hv⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨v', hVle hv'⟩)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ V)
    (hfix : Ew (toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hVle hψ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hVle hψ⟩) :
    ψ ∈ P := by

  let J : ↥V →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hVle)
  have hJ_apply : ∀ v : ↥V, J v = toCuspSubcarrier F hΦ₀ σ ξ ⟨v, hVle v.2⟩ := fun v => rfl
  have hJinj : Function.Injective J :=
    (toCuspSubcarrier_injective hΦ₀ σ ξ).comp (Submodule.inclusion_injective hVle)
  let W : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := LinearMap.range J
  haveI : FiniteDimensional ℂ ↥W := LinearMap.finiteDimensional_range J
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  haveI : CompleteSpace ↥W := FiniteDimensional.complete ℂ ↥W
  let Jeq : ↥V ≃ₗ[ℂ] ↥W := LinearEquiv.ofInjective J hJinj
  have hJeq_apply : ∀ v : ↥V, ((Jeq v : ↥W) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = J v :=
    fun v => LinearEquiv.ofInjective_apply J (h := hJinj) v

  have hSJ : ∀ (k : Kw F w) (v : ↥V),
      S k (J v) = J ⟨rightTranslate F (rowIsometryInclAt₀ F w k) v, hVst k v v.2⟩ := by
    intro k v
    rw [hJ_apply, hJ_apply]
    exact hS k ⟨v, hVle v.2⟩ (hVle (hVst k v v.2))
  have hSW : ∀ (k : Kw F w) (x : ↥W), S k x ∈ W := by
    rintro k ⟨_, v, rfl⟩
    exact ⟨_, (hSJ k v).symm⟩

  obtain ⟨_, hiff, _⟩ := hCI _ S hSn hSc Ew hEw
  have hfixJ : Ew (J ⟨ψ, hψ⟩) = J ⟨ψ, hψ⟩ := by rw [hJ_apply]; exact hfix
  obtain ⟨m, T, hT, x₁, hx₁⟩ := (hiff _).mp hfixJ

  have hSo : ∀ (k : Kw F w), ∀ z ∈ Wᗮ, S k z ∈ Wᗮ := by
    intro k z hz
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : S k⁻¹ u ∈ W := hSW k⁻¹ ⟨u, hu⟩
    have hku : S k (S k⁻¹ u) = u := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    let Sli : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗᵢ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
      { toLinearMap := (S k : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)), norm_map' := hSn k }
    have : ⟪S k (S k⁻¹ u), S k z⟫_ℂ = ⟪S k⁻¹ u, z⟫_ℂ := Sli.inner_map_map _ _
    rw [← hku, this]
    exact Submodule.inner_right_of_mem_orthogonal hu' hz
  have hpS : ∀ (k : Kw F w) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      W.starProjection (S k v) = S k (W.starProjection v) := by
    intro k v
    refine Submodule.eq_starProjection_of_mem_orthogonal (hSW k (W.orthogonalProjection v)) ?_
    rw [Submodule.starProjection_apply, ← map_sub]
    exact hSo k _ (Submodule.sub_starProjection_mem_orthogonal v)

  let T₂ : (Fin m → (Fin n → ℂ)) →L[ℂ] ↥W := W.orthogonalProjection.comp T
  have hT₂_coe : ∀ x, ((T₂ x : ↥W) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = W.starProjection (T x) := fun x => rfl
  have hT₂ : ∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)),
      ((T₂ (fun i => (ρc k).mulVec (x i)) : ↥W) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = S k (T₂ x) := by
    intro k x
    rw [hT₂_coe, hT, hpS, ← hT₂_coe]
  have hx₂ : T₂ x₁ = Jeq ⟨ψ, hψ⟩ := by
    apply Subtype.ext
    rw [hT₂_coe, hJeq_apply]
    have : T x₁ = J ⟨ψ, hψ⟩ := hx₁
    rw [this, ← hJeq_apply, ← Submodule.coe_orthogonalProjection_apply, Submodule.orthogonalProjection_mem_subspace_eq_self]

  have hJeqR : ∀ (k : Kw F w) (v : ↥V),
      ((Jeq ⟨rightTranslate F (rowIsometryInclAt₀ F w k) v, hVst k v v.2⟩ : ↥W) : ↥(cuspSubcarrier F hΦ₀ σ ξ))
        = S k (Jeq v) := by
    intro k v
    rw [hJeq_apply, hJeq_apply, hSJ]
  let T' : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    V.subtype.comp (Jeq.symm.toLinearMap.comp (T₂ : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] ↥W))
  have hT'_apply : ∀ x, T' x = ((Jeq.symm (T₂ x) : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) := fun x => rfl
  have hT' : ∀ (k : Kw F w) (x : Fin m → (Fin n → ℂ)),
      T' (fun j => (ρc k).mulVec (x j)) = fun y => T' x (y * rowIsometryInclAt₀ F w k) := by
    intro k x
    rw [hT'_apply, hT'_apply]
    set v : ↥V := Jeq.symm (T₂ x) with hv
    have hTx : T₂ x = Jeq v := by rw [hv, LinearEquiv.apply_symm_apply]
    have hTkx : T₂ (fun j => (ρc k).mulVec (x j))
        = Jeq ⟨rightTranslate F (rowIsometryInclAt₀ F w k) v, hVst k v v.2⟩ := by
      apply Subtype.ext
      rw [hT₂, hJeqR, hTx]
    rw [hTkx, LinearEquiv.symm_apply_apply]
    rfl
  have hψT' : T' x₁ = ψ := by
    rw [hT'_apply, hx₂, LinearEquiv.symm_apply_apply]

  have hblock : ∀ (j : Fin m) (z : Fin n → ℂ),
      T' (Pi.single j z) ∈ P := by
    intro j z
    refine hK1 (T'.comp (LinearMap.single ℂ (fun _ : Fin m => Fin n → ℂ) j)) ?_ z
    intro k x
    show T' (Pi.single j ((ρc k).mulVec x)) = fun y => T' (Pi.single j x) (y * rowIsometryInclAt₀ F w k)
    rw [← hT' k (Pi.single j x)]
    congr 1
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij, Matrix.mulVec_zero]
  rw [← hψT', ← Finset.univ_sum_single x₁, map_sum]
  exact P.sum_mem fun j _ => hblock j (x₁ j)

end Clause4w

section Incl

abbrev Kprod : Type := ∀ w : InfinitePlace F, Kw F w

omit [NumberField F] in
theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w)
    (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

noncomputable def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F) (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

variable {F}

theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

theorem rowIsometryInclAt₀_eq [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    rowIsometryInclAt₀ F w k = adelicArchGLIncl F (inclArch F (Pi.mulSingle w k)) := by
  rw [inclArch_mulSingle]; rfl

theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

theorem commute_adelicArchGLIncl_of_mem_finiteAdelicGL2Subgroup (x : GL (Fin 2) (InfiniteAdeleRing F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F) :
    Commute (adelicArchGLIncl F x) u := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hu
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hu, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_adelicArchGLIncl, mul_one, one_mul]

theorem rightTranslate_mul (a b : AdelicGL2 (𝓞 F) F) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (a * b) ψ = rightTranslate F a (rightTranslate F b ψ) := by
  funext x; simp [rightTranslate, mul_assoc]

theorem rightTranslate_one (ψ : AdelicGL2 (𝓞 F) F → ℂ) : rightTranslate F 1 ψ = ψ := by
  funext x; simp [rightTranslate]

end Incl

section Global

variable {F}
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
  [∀ w : InfinitePlace F, MeasurableSpace (Kw F w)] [∀ w : InfinitePlace F, BorelSpace (Kw F w)]
  (μ : ∀ w : InfinitePlace F, Measure (Kw F w))
  (S : ∀ w : InfinitePlace F, Kw F w →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
  (hS : ∀ (w : InfinitePlace F) (k : Kw F w),
    IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) (S w k))
  (hSn : ∀ (w : InfinitePlace F) (k : Kw F w) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖S w k v‖ = ‖v‖)
  (hSc : ∀ (w : InfinitePlace F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), Continuous fun k : Kw F w => S w k v)
  (n : InfinitePlace F → ℕ) (ρc : ∀ w : InfinitePlace F, Kw F w →* Matrix (Fin (n w)) (Fin (n w)) ℂ)
  (e : ∀ w : InfinitePlace F, Kw F w → ℂ)
  (hCI : ∀ (w : InfinitePlace F) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Kw F w →* (H →L[ℂ] H)), (∀ (k : Kw F w) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : Kw F w => π k v) →
      ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e w k) • (π k v) ∂(μ w)) →
        A.comp A = A ∧
        (∀ v : H, A v = v ↔
          ∃ (m : ℕ) (T : (Fin m → (Fin (n w) → ℂ)) →L[ℂ] H),
            (∀ (k : Kw F w) (x : Fin m → (Fin (n w) → ℂ)), T (fun i => (ρc w k).mulVec (x i)) = π k (T x)) ∧
            v ∈ LinearMap.range (T : (Fin m → (Fin (n w) → ℂ)) →ₗ[ℂ] H)) ∧
        (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin (n w) → ℂ)) →L[ℂ] H),
            (∀ (k : Kw F w) (x : Fin m → (Fin (n w) → ℂ)), T (fun i => (ρc w k).mulVec (x i)) = π k (T x)) ∧
            A v ∈ LinearMap.range (T : (Fin m → (Fin (n w) → ℂ)) →ₗ[ℂ] H)))
  (tys : ArchTypeFamily F)
  (hK1ii : ∀ (w : InfinitePlace F) (T : (Fin (n w) → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ (k : Kw F w) (x : Fin (n w) → ℂ), T ((ρc w k).mulVec x) = fun y => T x (y * rowIsometryInclAt₀ F w k)) →
      ∀ x : Fin (n w) → ℂ, T x ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
  (hK1iii : ∀ (w : InfinitePlace F), ∀ f ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i),
      (∀ y : AdelicGL2 (𝓞 F) F, Continuous fun k : Kw F w => f (y * rowIsometryInclAt₀ F w k)) →
      ∃ (m : ℕ) (T : (Fin m → (Fin (n w) → ℂ)) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)),
        (∀ (k : Kw F w) (x : Fin m → (Fin (n w) → ℂ)),
          T (fun j => (ρc w k).mulVec (x j)) = fun y => T x (y * rowIsometryInclAt₀ F w k)) ∧
        LinearMap.range T = Submodule.span ℂ (Set.range fun k : Kw F w =>
          fun y : AdelicGL2 (𝓞 F) F => f (y * rowIsometryInclAt₀ F w k)))
  (Ew : InfinitePlace F → (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
  (hEw : ∀ (w : InfinitePlace F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), Ew w v = ∫ k, (e w k) • (S w k v) ∂(μ w))
  (hEwstab : ∀ (w : InfinitePlace F) (W : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      IsClosed (W : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) → (∀ (k : Kw F w), ∀ x ∈ W, S w k x ∈ W) → ∀ x ∈ W, Ew w x ∈ W)
  (E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
  (hEfix : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (∀ w, Ew w v = v) → E v = v)
  (hEwE : ∀ (w : InfinitePlace F) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), Ew w (E v) = E v)
  (hEstab : ∀ (W : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      IsClosed (W : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) → (∀ (w : InfinitePlace F) (k : Kw F w), ∀ x ∈ W, S w k x ∈ W) →
      ∀ x ∈ W, E x ∈ W)

include hS hSn hSc hCI hK1iii hEw hEfix in

theorem clause3 (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hφt : φ ∈ archCutSubmodule F tys) :
    E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ := by
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  refine hEfix _ fun w => ?_
  have hφw : φ ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) :=
    (mem_archCutSubmodule_iff F tys φ).mp hφt w
  have hφc : ∀ y : AdelicGL2 (𝓞 F) F, Continuous fun k : Kw F w => φ (y * rowIsometryInclAt₀ F w k) :=
    fun y => hφ.2.comp (continuous_const.mul (continuous_rowIsometryInclAt₀ w))
  obtain ⟨m, T, hT, hTr⟩ := hK1iii w φ hφw hφc
  have hA := (hCI w _ (S w) (hSn w) (hSc w) (Ew w) (hEw w)).2.1
  exact apply_toCuspSubcarrier_eq_of_range_eq_span hΦ₀ σ ξ w (S w) (hS w) (ρc w) (Ew w)
    (fun v hv => (hA v).mpr hv) φ hφ T hT hTr

include hS hSn hSc hCI hK1ii hEw hEwstab hEwE hEstab in

theorem clause4 (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hφK : ∃ tys' : ArchTypeFamily F, φ ∈ archCutSubmodule F tys') :
    ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
      φ' ∈ archCutSubmodule F tys ∧
      (∀ U : Subgroup (AdelicGL2 (𝓞 F) F), U ≤ finiteAdelicGL2Subgroup F →
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) → ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧
      (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ ψ ∈ V,
          rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ V) → φ ∈ V → φ' ∈ V) ∧
      E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩ := by
  classical
  obtain ⟨tys', hφt⟩ := hφK
  obtain ⟨hfd, -, -, hstab⟩ := finiteDimensional_span_translates_of_mem_archCutSubmodule F (inclArch F)
    archComponent_inclArch tys' φ hφ.2 hφt
  set V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun κ : Kprod F =>
    fun g : AdelicGL2 (𝓞 F) F => φ (g * adelicArchGLIncl F (inclArch F κ))) with hVdef
  haveI : FiniteDimensional ℂ ↥V := hfd
  have hVle : V ≤ cuspMemberSubmodule F Φ₀ ξ := by
    rw [Submodule.span_le]
    rintro _ ⟨κ, rfl⟩
    exact rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (adelicArchGLIncl F (inclArch F κ)) φ hφ
  have hVst : ∀ (w : InfinitePlace F) (k : Kw F w), ∀ v ∈ V, rightTranslate F (rowIsometryInclAt₀ F w k) v ∈ V := by
    intro w k v hv
    rw [rowIsometryInclAt₀_eq]
    exact hstab v hv (Pi.mulSingle w k)
  have hφV : φ ∈ V := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g; simp

  let J : ↥V →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hVle)
  have hJ_apply : ∀ v : ↥V, J v = toCuspSubcarrier F hΦ₀ σ ξ ⟨v, hVle v.2⟩ := fun v => rfl
  let W : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := LinearMap.range J
  haveI : FiniteDimensional ℂ ↥W := LinearMap.finiteDimensional_range J
  have hWc : IsClosed (W : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := Submodule.closed_of_finiteDimensional W
  have hSW : ∀ (w : InfinitePlace F) (k : Kw F w), ∀ x ∈ W, S w k x ∈ W := by
    rintro w k _ ⟨v, rfl⟩
    refine ⟨⟨rightTranslate F (rowIsometryInclAt₀ F w k) v, hVst w k v v.2⟩, ?_⟩
    rw [hJ_apply, hJ_apply]
    exact (hS w k ⟨v, hVle v.2⟩ (hVle (hVst w k v v.2))).symm

  obtain ⟨⟨φ', hφ'V⟩, hJφ'⟩ := hEstab W hWc hSW (J ⟨φ, hφV⟩) ⟨⟨φ, hφV⟩, rfl⟩
  have hEφ : E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hVle hφ'V⟩ := hJφ'.symm
  refine ⟨φ', hVle hφ'V, ?_, ?_, ?_, hEφ⟩
  ·
    rw [mem_archCutSubmodule_iff]
    intro w
    have hEwV : ∀ v (hv : v ∈ V), ∃ v' : AdelicGL2 (𝓞 F) F → ℂ, ∃ hv' : v' ∈ V,
        Ew w (toCuspSubcarrier F hΦ₀ σ ξ ⟨v, hVle hv⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨v', hVle hv'⟩ := by
      intro v hv
      obtain ⟨⟨v', hv'⟩, h⟩ := hEwstab w W hWc (hSW w) (J ⟨v, hv⟩) ⟨⟨v, hv⟩, rfl⟩
      exact ⟨v', hv', h.symm⟩
    have hfix : Ew w (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hVle hφ'V⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hVle hφ'V⟩ := by
      rw [← hEφ, hEwE]
    exact mem_of_apply_toCuspSubcarrier_eq hΦ₀ σ ξ w (μ w) (S w) (hS w) (hSn w) (hSc w) (ρc w) (e w) (hCI w)
      _ (hK1ii w) (Ew w) (hEw w) V hVle (hVst w) hEwV φ' hφ'V hfix
  ·
    intro U hU hφU
    suffices h : ∀ v ∈ V, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, v (g * k) = v g from h φ' hφ'V
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, v (g * k) = v g)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨κ, rfl⟩ g k hk
      show φ (g * k * adelicArchGLIncl F (inclArch F κ)) = φ (g * adelicArchGLIncl F (inclArch F κ))
      rw [mul_assoc, ← (commute_adelicArchGLIncl_of_mem_finiteAdelicGL2Subgroup (inclArch F κ) (hU hk)).eq,
        ← mul_assoc]
      exact hφU _ k hk
    · intro g k hk; rfl
    · intro a b _ _ ha hb g k hk
      show a (g * k) + b (g * k) = a g + b g
      rw [ha g k hk, hb g k hk]
    · intro c a _ ha g k hk
      show c • a (g * k) = c • a g
      rw [ha g k hk]
  ·
    intro V' hV' hφV'
    suffices h : V ≤ V' from h hφ'V
    rw [Submodule.span_le]
    rintro _ ⟨κ, rfl⟩
    have key : ∀ κ : Kprod F, ∀ ψ ∈ V', rightTranslate F (adelicArchGLIncl F (inclArch F κ)) ψ ∈ V' := by
      intro κ
      rw [← Finset.noncommProd_mulSingle κ]
      refine Finset.noncommProd_induction _ _ _
        (fun x : Kprod F => ∀ ψ ∈ V', rightTranslate F (adelicArchGLIncl F (inclArch F x)) ψ ∈ V') ?_ ?_ ?_
      · intro a b ha hb ψ hψ
        rw [map_mul, map_mul, rightTranslate_mul]
        exact ha _ (hb ψ hψ)
      · intro ψ hψ
        rw [map_one, map_one, rightTranslate_one]
        exact hψ
      · intro w _ ψ hψ
        rw [← rowIsometryInclAt₀_eq]
        exact hV' w (κ w) ψ hψ
    exact key κ φ hφV'

end Global

end ParchProof34

end

open ParchProof in
open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (tys : ArchTypeFamily F) :
    ∃ E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      E.comp E = E ∧
      (∀ M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M → M.map (E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        φ ∈ archCutSubmodule F tys →
        E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∃ tys' : ArchTypeFamily F, φ ∈ archCutSubmodule F tys') →
        ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
          φ' ∈ archCutSubmodule F tys ∧
          (∀ U : Subgroup (AdelicGL2 (𝓞 F) F), U ≤ finiteAdelicGL2Subgroup F →
            (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) → ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧
          (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ ψ ∈ V,
              rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ V) → φ ∈ V → φ' ∈ V) ∧
          E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩) ∧
      (∀ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S → S.comp Tc = Tc.comp S) →
        E.comp Tc = Tc.comp E) ∧
      (∀ g ∈ finiteAdelicGL2Subgroup F, ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S → E.comp S = S.comp E) := by
  refine ⟨E F hΦ₀ σ ξ hσ tys, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← ContinuousLinearMap.mul_def]
    exact E_mul_E F hΦ₀ σ ξ hσ tys
  ·
    intro M hM x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine E_apply_mem F hΦ₀ σ ξ hσ tys M (fun w z hz => ?_) y hy
    refine Ew_apply_mem F hΦ₀ σ ξ hσ tys w M hM.isClosed (fun c u hu => ?_) z hz
    exact hM.map_le_of_rightTranslate_arch w c _ (isCuspLift_Sw F hΦ₀ σ ξ hσ w c) (Submodule.mem_map_of_mem hu)
  ·
    intro φ hφ hφt
    exact ParchProof34.clause3 hΦ₀ σ ξ (ParchProof.μw F) (ParchProof.Sw F hΦ₀ σ ξ hσ)
      (ParchProof.isCuspLift_Sw F hΦ₀ σ ξ hσ) (ParchProof.norm_Sw_apply F hΦ₀ σ ξ hσ)
      (ParchProof.continuous_Sw_apply F hΦ₀ σ ξ hσ) (ParchProof.nw F tys) (ParchProof.ρc F tys) (ParchProof.ew F tys)
      (ParchProof.ew_isotypic F tys) tys
      (fun w => ((ParchProof.ρc_spec F tys w) _ (rowIsometryInclAt₀ F w) (ParchProof.injective_rowIsometryInclAt₀ w)).2)
      (ParchProof.Ew F hΦ₀ σ ξ hσ tys) (ParchProof.Ew_apply F hΦ₀ σ ξ hσ tys) (ParchProof.E F hΦ₀ σ ξ hσ tys)
      (fun v h => ParchProof.E_apply_eq_self F hΦ₀ σ ξ hσ tys h) φ hφ hφt
  ·
    intro φ hφ hφK
    exact ParchProof34.clause4 hΦ₀ σ ξ (ParchProof.μw F) (ParchProof.Sw F hΦ₀ σ ξ hσ)
      (ParchProof.isCuspLift_Sw F hΦ₀ σ ξ hσ) (ParchProof.norm_Sw_apply F hΦ₀ σ ξ hσ)
      (ParchProof.continuous_Sw_apply F hΦ₀ σ ξ hσ) (ParchProof.nw F tys) (ParchProof.ρc F tys) (ParchProof.ew F tys)
      (ParchProof.ew_isotypic F tys) tys
      (fun w => ((ParchProof.ρc_spec F tys w) _ (rowIsometryInclAt₀ F w) (ParchProof.injective_rowIsometryInclAt₀ w)).1)
      (ParchProof.Ew F hΦ₀ σ ξ hσ tys) (ParchProof.Ew_apply F hΦ₀ σ ξ hσ tys)
      (ParchProof.Ew_apply_mem F hΦ₀ σ ξ hσ tys) (ParchProof.E F hΦ₀ σ ξ hσ tys)
      (ParchProof.Ew_apply_E_apply F hΦ₀ σ ξ hσ tys)
      (fun W hW hSW => ParchProof.E_apply_mem F hΦ₀ σ ξ hσ tys W (fun w => ParchProof.Ew_apply_mem F hΦ₀ σ ξ hσ tys w W hW (hSW w)))
      φ hφ hφK
  ·
    intro Tc hTc
    have h : Commute Tc (E F hΦ₀ σ ξ hσ tys) := commute_E F hΦ₀ σ ξ hσ tys fun w =>
      commute_Ew_of F hΦ₀ σ ξ hσ tys w Tc fun c => by
        have e := hTc w c _ (isCuspLift_Sw F hΦ₀ σ ξ hσ w c)
        rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at e
        exact e.symm
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
    exact h.eq.symm
  ·
    intro g hg S hS
    have h : Commute S (E F hΦ₀ σ ξ hσ tys) := commute_E F hΦ₀ σ ξ hσ tys fun w =>
      commute_Ew_of F hΦ₀ σ ξ hσ tys w S fun c => by
        have e := comp_eq_comp_of_isCuspLift_rightTranslate
          (commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup hg w c) hS (isCuspLift_Sw F hΦ₀ σ ξ hσ w c)
        rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at e
        exact e
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
    exact h.eq.symm

end S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector (solution)
