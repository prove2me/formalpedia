-- Prove2me | solution 1 for AutomorphicForm.countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0b994a66-74c6-5d22-8bb3-cabde227a21b

import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option linter.deprecated false

open scoped ENNReal NNReal

noncomputable section

namespace CountReduce

open Filter Topology AutomorphicForm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem countable_of_orthonormal [IsSeparable μ] {ι : Type*} (b : ι → X → ℂ)
    (hbm : ∀ i, AEStronglyMeasurable (b i) μ)
    (hb₁ : ∀ i, ∫ x, b i x * conj (b i x) ∂μ = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ x, b i x * conj (b j x) ∂μ = 0) : Countable ι := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

  have hint : ∀ i, Integrable (fun x => b i x * conj (b i x)) μ := by
    intro i
    by_contra h
    have h1 := hb₁ i
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  have hL2 : ∀ i, MemLp (b i) 2 μ := by
    intro i
    refine (memLp_two_iff_integrable_sq_norm (hbm i)).2 ((hint i).norm.congr ?_)
    filter_upwards with x
    rw [norm_mul, RCLike.norm_conj, sq]

  set v : ι → Lp ℂ 2 μ := fun i => (hL2 i).toLp with hv
  have hinner : ∀ i j, inner ℂ (v i) (v j) = conj (∫ x, b i x * conj (b j x) ∂μ) := by
    intro i j
    rw [L2.inner_def, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [(hL2 i).coeFn_toLp, (hL2 j).coeFn_toLp] with x hx hy
    simp only [hv, hx, hy, RCLike.inner_apply, map_mul, RCLike.conj_conj, mul_comm]
  have horth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner]
    split_ifs with h
    · subst h; rw [hb₁, map_one]
    · rw [hb₀ i j h, map_zero]

  have hdist : ∀ i j, i ≠ j → (1 : ℝ) ≤ ‖v i - v j‖ := by
    intro i j hij
    have h2 : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq ℂ, horth.1 i, horth.1 j, (orthonormal_iff_ite.1 horth) i j, if_neg hij]
      simp
      norm_num
    nlinarith [norm_nonneg (v i - v j)]

  have hpd : (Set.univ : Set ι).PairwiseDisjoint fun i => Metric.ball (v i) (1 / 2) := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun z hzi hzj => ?_
    have h1 := hdist i j hij
    have h2 : dist (v i) (v j) < 1 := by
      calc dist (v i) (v j) ≤ dist (v i) z + dist z (v j) := dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (by rw [dist_comm]; exact hzi) hzj
        _ = 1 := by norm_num
    rw [dist_eq_norm] at h2
    linarith
  have hcnt : (Set.univ : Set ι).Countable :=
    hpd.countable_of_isOpen (fun i _ => Metric.isOpen_ball)
      (fun i _ => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.1 hcnt

end CountReduce

end

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (tys : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S ∧
      b i ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0)
    (hbs : ∀ π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys) :
    Countable ι := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K) := inferInstance
  haveI : MeasurableSpace.CountablyGenerated (AdelicGL2 (𝓞 K) K) := inferInstance
  haveI : IsSeparable ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := inferInstance
  have hbc : ∀ i, Continuous (b i) := fun i =>
    continuous_of_mem_isotypicCuspSubmodule (Submodule.mem_inf.mp (hb i).2).1
  exact CountReduce.countable_of_orthonormal (μ := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) b
    (fun i => (hbc i).aestronglyMeasurable) hb₁ hb₀

end S_AutomorphicForm_countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab (solution)
