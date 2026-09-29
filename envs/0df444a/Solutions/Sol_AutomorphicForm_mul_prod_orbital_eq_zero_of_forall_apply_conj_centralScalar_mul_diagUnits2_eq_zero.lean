-- Prove2me | solution 1 for AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f2fc0acf-3b99-55d4-af11-a2ef59a46393

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_mul_prod_eq_zero_of_forall_apply_conj_eq_zero_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.localCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace HWBook
variable (K : Type) [Field K] [NumberField K]

theorem val_centralScalar_mul_diagUnits2 (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(z : (AdeleRing (𝓞 K) K)) * a, 0; 0, (z : (AdeleRing (𝓞 K) K)) * b] := by
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Matrix.diagonal_apply]

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    g * AutomorphicForm.centralScalar (𝓞 K) K z = AutomorphicForm.centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (z : (AdeleRing (𝓞 K) K)) =
    Matrix.scalar (Fin 2) (z : (AdeleRing (𝓞 K) K)) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact ((Matrix.scalar_commute (z : (AdeleRing (𝓞 K) K)) (fun r' => mul_comm _ r') _).eq).symm

theorem inv_diagUnits2 {R : Type} [CommRing R] (x y : Rˣ) : (diagUnits2 x y)⁻¹ = diagUnits2 x⁻¹ y⁻¹ :=
  Units.ext rfl

theorem glArch_gamma_eq (u : Kˣ) (a z : (AdeleRing (𝓞 K) K)ˣ)
    (h : ((a : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)).1 = ((z : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)).1) :
    AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K a *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) =
      AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) := by
  rw [AutomorphicForm.glArch_centralScalar_mul_diagUnits2, AutomorphicForm.glArch_centralScalar_mul_diagUnits2,
    show Units.map (AdelicLevel.adeleArch (𝓞 K) K : (AdeleRing (𝓞 K) K) →* InfiniteAdeleRing K) a =
      Units.map (AdelicLevel.adeleArch (𝓞 K) K : (AdeleRing (𝓞 K) K) →* InfiniteAdeleRing K) z from Units.ext h]

theorem isRegularSemisimple_gamma (u : Kˣ) (hu1 : (u : K) ≠ 1) (a : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.centralScalar (𝓞 K) K a *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) := by
  unfold AutomorphicForm.IsRegularSemisimple
  rw [val_centralScalar_mul_diagUnits2, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have hU : IsUnit ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)) - 1) := by
    rw [Units.coe_map, MonoidHom.coe_coe, ← map_one (algebraMap K (AdeleRing (𝓞 K) K)), ← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu1)).map _
  have e : ((a : (AdeleRing (𝓞 K) K)) * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)) + (a : (AdeleRing (𝓞 K) K)) * ((1 : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))) ^ 2 -
      4 * ((a : (AdeleRing (𝓞 K) K)) * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)) * ((a : (AdeleRing (𝓞 K) K)) * ((1 : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))) - 0 * 0) =
      ((a : (AdeleRing (𝓞 K) K)) * ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)) - 1)) ^ 2 := by
    rw [Units.val_one]; ring
  rw [e]
  exact (a.isUnit.mul hU).pow 2

theorem finComponent_gamma_mem_localIntegralSet (u : Kˣ) (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (ha : ((((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hu : NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) :
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K a *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) ∈
      AutomorphicForm.localIntegralSet K v := by
  obtain ⟨hi1, hi2⟩ := (NumberField.Idele.ord_eq_zero_iff K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)).mp hu
  have hU : (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ v.adicCompletionIntegers K := hi1
  have hU' : (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ v.adicCompletionIntegers K := hi2
  have h1 : ((((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := rfl
  have ha' : ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
    have hm : ((((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by rw [mul_inv_cancel]; rfl
    have hm' : ((((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := hm
    rwa [ha, one_mul] at hm'

  have hinv : ((AutomorphicForm.centralScalar (𝓞 K) K a *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))⁻¹ =
      AutomorphicForm.centralScalar (𝓞 K) K a⁻¹ * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ 1 := by
    rw [mul_inv_rev, inv_diagUnits2, inv_one, ← map_inv (AutomorphicForm.centralScalar (𝓞 K) K) a,
      mul_centralScalar_comm]
  rw [AutomorphicForm.mem_localIntegralSet]
  constructor
  · intro i j
    rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, ha, h1, one_mul, one_mul,
      Matrix.diagonal_apply]
    split_ifs
    · fin_cases i
      · exact hU
      · exact one_mem _
    · exact zero_mem _
  · intro i j
    rw [← map_inv, ← map_inv, hinv, AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, ha', h1,
      one_mul, one_mul, Matrix.diagonal_apply]
    split_ifs
    · fin_cases i
      · exact hU'
      · exact one_mem _
    · exact zero_mem _

theorem finComponent_gamma_eq_of_coe_eq (u : Kˣ) (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K)
    (ha : ((((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = x)
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![x * algebraMap K (v.adicCompletion K) (u : K), x]) :
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K a *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) = g := by
  apply Units.ext
  have h1 : ((((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := rfl
  have hu' : (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = algebraMap K (v.adicCompletion K) (u : K) := rfl
  rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, hg, ha, h1, hu', mul_one]

theorem finComponent_gamma_eq_of_snd_eq (u : Kˣ) (a z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : ((((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = ((((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) :
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K a *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) =
      AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) := by
  apply Units.ext
  rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2,
    AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, h]

end HWBook

namespace HwinCore

section Arch

variable {A : Type} [CommRing A] [TopologicalSpace A]

theorem isOrbitalIntegralOn_of_eq_smul
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A)) (γ : GL (Fin 2) A)
    (τ τ' : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (c : ℝ≥0) (h : τ = c • τ') (f : GL (Fin 2) A → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn A μ γ τ f I) :
    AutomorphicForm.IsOrbitalIntegralOn A μ γ τ' f (((c : ℝ) : ℂ) * I) := by
  letI := AutomorphicForm.glBorelOf A
  obtain ⟨w, ⟨hw0, hwm, hwc, hws⟩, hIw⟩ := hI
  refine ⟨fun x => (c : ℝ) * w x, ⟨fun x => mul_nonneg c.coe_nonneg (hw0 x), hwm.const_mul _, hwc.mul_left,
    fun x hx => ?_⟩, ?_⟩
  · have h1 := hws x hx
    rw [h, integral_smul_nnreal_measure] at h1
    rw [integral_const_mul]
    simpa [NNReal.smul_def, smul_eq_mul] using h1
  · rw [hIw, ← integral_const_mul]
    congr 1
    funext x
    push_cast
    ring

end Arch

section Transport

variable (K : Type) [Field K] [NumberField K]

theorem arch_transport
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    {γ γ' : GL (Fin 2) (InfiniteAdeleRing K)} (h : γ = γ')
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
    (τ' : Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
    [τ.IsHaarMeasure] [τ'.IsHaarMeasure]
    [SecondCountableTopology (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (InfiniteAdeleRing K))))]
    [LocallyCompactSpace (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (InfiniteAdeleRing K))))]
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν γ τ f I) :
    ∃ c : ℝ≥0, 0 < c ∧ AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν γ' τ' f (((c : ℝ) : ℂ) * I) := by
  subst h
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  have hs : τ = Measure.haarScalarFactor τ τ' • τ' := Measure.isMulLeftInvariant_eq_smul τ τ'
  exact ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure τ τ',
    isOrbitalIntegralOn_of_eq_smul ν γ τ τ' _ hs f I hI⟩

theorem fin_transport (v : HeightOneSpectrum (𝓞 K))
    {g g' : GL (Fin 2) (v.adicCompletion K)} (h : g = g')
    (τ : Measure (AutomorphicForm.localCentralizer K v g)) (τ' : Measure (AutomorphicForm.localCentralizer K v g'))
    [τ.IsHaarMeasure] [τ'.IsHaarMeasure]
    [SecondCountableTopology (AutomorphicForm.localCentralizer K v g')]
    [LocallyCompactSpace (AutomorphicForm.localCentralizer K v g')]
    (h1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (h1' : τ' (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v g τ f I) :
    AutomorphicForm.IsOrbitalIntegral K v g' τ' f I := by
  subst h
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v g) := ⟨rfl⟩
  have hs : τ = Measure.haarScalarFactor τ τ' • τ' := Measure.isMulLeftInvariant_eq_smul τ τ'
  have hc : Measure.haarScalarFactor τ τ' = 1 := by
    have h2 := congrArg (fun μ : Measure (AutomorphicForm.localCentralizer K v g) =>
      μ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v)) hs
    simp only [Measure.smul_apply, h1, h1', ENNReal.smul_def, smul_eq_mul, mul_one] at h2
    exact_mod_cast h2.symm
  rw [hc, one_smul] at hs
  exact hs ▸ hI

end Transport

end HwinCore

open HwinCore in
set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (hind : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T →
      NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (S ∪ T) f fa ff fS)
    (hcen : ∀ v ∈ T, ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fS v (c * y) = fS v y)

    (hvan : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      f (x⁻¹ * ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) * x) = 0)
    (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (τG : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ z, (τG z).IsHaarMeasure)
    (hτGc : ∀ z, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA z))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z v, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z v))
    (hτF1 : ∀ z v, τF z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA z) →
        (∀ v ∈ S', AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S', WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG z) = cT * (∫ t, Wa t ∂(τA z)) * ∏ v ∈ S', ∫ t, WS v t ∂(τF z v))

    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v))

    (ϖT : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) (hϖT : ∀ v ∈ T, Irreducible (ϖT v))
    (eT : HeightOneSpectrum (𝓞 K) → ℤ)
    (tT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (htT : ∀ v ∈ T, (tT v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖT v : v.adicCompletion K) ^ eT v * algebraMap K (v.adicCompletion K) (u : K),
        (ϖT v : v.adicCompletion K) ^ eT v])
    (hshell : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      ∃ (τ : @Measure (AutomorphicForm.localCentralizer K v (tT v)) (AutomorphicForm.localCentralizerBorel K v (tT v)))
        (I : ℂ), @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (tT v)) τ ∧
          τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 ∧
          AutomorphicForm.IsOrbitalIntegral K v (tT v) τ (fS v) I ∧ I ≠ 0)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    IA z * ∏ v ∈ S, IF z v = 0 := by
  classical

  have hϖ : ∀ v ∈ T, ((ϖT v : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro v hv h0
    exact (hϖT v hv).ne_zero (by exact_mod_cast h0)
  let x : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun v =>
    if hv : v ∈ T then (Units.mk0 ((ϖT v : v.adicCompletionIntegers K) : v.adicCompletion K) (hϖ v hv)) ^ eT v else 1
  have hx : ∀ v ∈ T, ((x v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((ϖT v : v.adicCompletionIntegers K) : v.adicCompletion K) ^ eT v := by
    intro v hv
    simp only [x, dif_pos hv, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  obtain ⟨zs, hz1, hzS, hzT, hz0⟩ :=
    NumberField.Idele.exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one K S T z x
  have hTS' : ∀ v ∈ T, v ∉ S := fun v hv => Finset.disjoint_left.1 hTS hv

  have hreg := HWBook.isRegularSemisimple_gamma K u hu1 zs
  have hint : ∀ v ∉ S ∪ T, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K zs *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) ∈
      AutomorphicForm.localIntegralSet K v := by
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    exact HWBook.finComponent_gamma_mem_localIntegralSet K u zs v (hz0 v hv.1 hv.2) (hind v hv.1 hv.2)
  have harch := HWBook.glArch_gamma_eq K u zs z hz1
  have hSCLC := AutomorphicForm.centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
      K (AutomorphicForm.centralScalar (𝓞 K) K zs *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)

  letI mGL : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
  obtain ⟨c, hc, hIa⟩ : ∃ c : ℝ≥0, 0 < c ∧ AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K zs *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
      (τA zs) fa (((c : ℝ) : ℂ) * IA z) := by
    haveI := hSCLC.2.2.1
    haveI := hSCLC.2.2.2.1
    haveI := hτA zs
    haveI := hτA z
    exact arch_transport K νA harch.symm (τA z) (τA zs) fa (IA z) (hIA z)

  have hshell' : ∀ v ∈ T, ∃ I : ℂ, I ≠ 0 ∧ AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K zs *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
      (τF zs v) (fS v) I := by
    intro v hv
    obtain ⟨τ, I, hτ, hτ1, hI, hI0⟩ := hshell v hv
    have heq := HWBook.finComponent_gamma_eq_of_coe_eq K u zs v _ ((hzT v hv (hTS' v hv)).trans (hx v hv))
      (tT v) (htT v hv)
    haveI := (hSCLC.2.2.2.2.1 v).1
    haveI := (hSCLC.2.2.2.2.1 v).2
    haveI := hτ
    haveI := hτF zs v
    exact ⟨I, hI0, fin_transport K v heq.symm τ (τF zs v) hτ1 (hτF1 zs v) (fS v) I hI⟩
  choose! IT hIT using hshell'
  have hIS : ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K zs *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
      (τF zs v) (fS v) (IF z v) := by
    intro v hv
    have heq := HWBook.finComponent_gamma_eq_of_snd_eq K u zs z v (hzS v hv)
    haveI := (hSCLC.2.2.2.2.1 v).1
    haveI := (hSCLC.2.2.2.2.1 v).2
    haveI := hτF z v
    haveI := hτF zs v
    exact fin_transport K v heq.symm (τF z v) (τF zs v) (hτF1 z v) (hτF1 zs v) (fS v) (IF z v) (hIF z v hv)

  let Iv : HeightOneSpectrum (𝓞 K) → ℂ := fun v => if v ∈ S then IF z v else IT v
  have hIv : ∀ v ∈ S ∪ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K zs *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
      (τF zs v) (fS v) (Iv v) := by
    intro v hv
    rcases Finset.mem_union.1 hv with hS | hT
    · simp only [Iv, if_pos hS]
      exact hIS v hS
    · simp only [Iv, if_neg (hTS' v hT)]
      exact (hIT v hT).2
  have key := AutomorphicForm.mul_prod_eq_zero_of_forall_apply_conj_eq_zero_of_isUnitFactorization K
    (adelicGLHaar (Fin 2) (𝓞 K) K) (isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K) νA cG hG
    (AutomorphicForm.centralScalar (𝓞 K) K zs *
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)
    hreg (τG zs) (hτG zs) (τA zs) (hτA zs) (τF zs) (hτF zs) (hτF1 zs) cT hcT (hT zs) (S ∪ T)
    f fa ff fS hf hint (hvan zs) _ hIa Iv hIv

  rw [Finset.prod_union hTS.symm] at key
  have hS' : ∏ v ∈ S, Iv v = ∏ v ∈ S, IF z v := Finset.prod_congr rfl fun v hv => if_pos hv
  have hT' : ∏ v ∈ T, Iv v ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v hv => by
      simp only [Iv, if_neg (hTS' v hv)]
      exact (hIT v hv).1
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [hS'] at key
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h1 | h2
    · exact absurd h1 hc'
    · rw [h2, zero_mul]
  · rcases mul_eq_zero.1 h with h3 | h4
    · rw [h3, mul_zero]
    · exact absurd h4 hT'

end S_AutomorphicForm_mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero (solution)
