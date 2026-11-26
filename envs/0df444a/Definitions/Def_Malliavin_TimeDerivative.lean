-- Prove2me | Definitions.Def_Malliavin_TimeDerivative
-- name    : Malliavin_TimeDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:10:08.642844+00:00
-- url     : https://prove2.me/theorems/2f23fcda-294f-4254-aa74-553195eaf438
-- title:
--   Time Derivative
-- statement:
--   Definitions and structural lemmas for Time Derivative, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_integral_coe_eq_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_space_hasGaussianLaw
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsSmoothBounded_cylindrical
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_range_wienerIntegral
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
section CompLp
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
theorem inner_compLpL_compLpL (L : E →ₗᵢ[ℝ] F) (f g : Lp E 2 μ) :
    ⟪L.toContinuousLinearMap.compLpL 2 μ f, L.toContinuousLinearMap.compLpL 2 μ g⟫_ℝ =
      ⟪f, g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [L.toContinuousLinearMap.coeFn_compLpL f,
    L.toContinuousLinearMap.coeFn_compLpL g] with ω h1 h2
  rw [h1, h2, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map]
noncomputable def compLpₗᵢ (L : E →ₗᵢ[ℝ] F) : Lp E 2 μ →ₗᵢ[ℝ] Lp F 2 μ :=
  ⟨(L.toContinuousLinearMap.compLpL 2 μ).toLinearMap, fun f ↦ by
    have h := inner_compLpL_compLpL L f f
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h⟩
theorem coeFn_compLpₗᵢ (L : E →ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    (compLpₗᵢ L f : Ω → F) =ᵐ[μ] fun ω ↦ L (f ω) :=
  L.toContinuousLinearMap.coeFn_compLpL f
theorem compLpₗᵢ_comp_compLpₗᵢ (e : E ≃ₗᵢ[ℝ] F) (f : Lp F 2 μ) :
    compLpₗᵢ e.toLinearIsometry (compLpₗᵢ e.symm.toLinearIsometry f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ e.toLinearIsometry (compLpₗᵢ e.symm.toLinearIsometry f),
    coeFn_compLpₗᵢ e.symm.toLinearIsometry f] with ω h1 h2
  rw [h1, h2, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]
noncomputable def compLpEquiv (e : E ≃ₗᵢ[ℝ] F) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp F 2 μ :=
  LinearIsometryEquiv.ofSurjective (compLpₗᵢ e.toLinearIsometry) fun f ↦
    ⟨compLpₗᵢ e.symm.toLinearIsometry f, compLpₗᵢ_comp_compLpₗᵢ e f⟩
end CompLp
section WienerEquiv
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
noncomputable def wienerIntegralEquiv (hB : IsPreBrownianReal B P) :
    Lp ℝ 2 nonnegativeLebesgueMeasure ≃ₗᵢ[ℝ] firstChaos hB :=
  (wienerIntegralₗᵢ hB).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (range_wienerIntegral hB))
end WienerEquiv
section TimeDerivative
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} [SFinite P]
noncomputable def timeDerivativeOfFirstChaos (hB : IsPreBrownianReal B P) :
    Lp (firstChaos hB) 2 P →ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  fubiniLift.comp (compLpₗᵢ (wienerIntegralEquiv hB).symm.toLinearIsometry)
end TimeDerivative
section CameronMartin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
theorem brownianLp_eq_ofDual (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) :
    brownianLp hB t = (ofDual P (L t) : Lp ℝ 2 P) := by
  have hmean : L t (mean P) = 0 := by
    rw [mean, ← IsGaussian.integral_dual (L t), ← hB.integral_eval t]
    congr 1
    funext w
    exact (hL t w).symm
  apply Lp.ext
  filter_upwards [coeFn_brownianLp hB t, centeredDualToLp_ae_eq P (L t)] with w h1 h2
  rw [h1, coe_ofDual, h2, hmean, sub_zero, hL]
theorem firstChaos_le_space (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) :
    firstChaos hB ≤ Space P := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  rw [brownianLp_eq_ofDual hB L hL t]
  exact (ofDual P (L t)).2
noncomputable def timeDerivativeOfEq (hB : IsPreBrownianReal B P)
    (hS : Space P = firstChaos hB) :
    Lp (Space P) 2 P →ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  (timeDerivativeOfFirstChaos hB).comp
    (compLpₗᵢ (LinearIsometryEquiv.ofEq _ _ hS).toLinearIsometry)
theorem brownianLp_mem_space (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t ∈ Space P := by
  rw [brownianLp_eq_ofDual hB L hL t]
  exact (ofDual P (L t)).2
noncomputable def spaceVector (B : ℝ≥0 → W → ℝ) (Z : RandomL2 P) (I : Finset ℝ≥0) (w : W) :
    ℝ × (I → ℝ) :=
  (Z w, fun i ↦ B i w)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
theorem aemeasurable_spaceVector (hB : IsPreBrownianReal B P) (Z : RandomL2 P)
    (I : Finset ℝ≥0) : AEMeasurable (spaceVector B Z I) P := by
  refine AEMeasurable.prodMk (Lp.aestronglyMeasurable Z).aemeasurable ?_
  exact aemeasurable_pi_lambda _ fun i ↦ hB.aemeasurable i
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- A linear functional of `spaceVector` is a.e. a linear combination of `Z` and the `B i`. -/
theorem coeFn_combination_spaceVector (hB : IsPreBrownianReal B P) (Z : RandomL2 P)
    (I : Finset ℝ≥0) (ℓ : (ℝ × (I → ℝ)) →L[ℝ] ℝ) :
    ((ℓ (1, 0) • Z + ∑ i : I, ℓ (0, Pi.single i 1) • brownianLp hB i : RandomL2 P) : W → ℝ)
      =ᵐ[P] fun w ↦ ℓ (spaceVector B Z I w) := by
  have hsum := Lp.coeFn_finsetSum (μ := P) Finset.univ
    (fun i : I ↦ ℓ (0, Pi.single i 1) • brownianLp hB i)
  have hB' : ∀ᵐ w ∂P, ∀ i : I, (brownianLp hB i : W → ℝ) w = B i w :=
    ae_all_iff.2 fun i ↦ coeFn_brownianLp hB i
  have hsmul : ∀ᵐ w ∂P, ∀ i : I,
      ((ℓ (0, Pi.single i 1) • brownianLp hB i : RandomL2 P) : W → ℝ) w =
        ℓ (0, Pi.single i 1) * (brownianLp hB i : W → ℝ) w :=
    ae_all_iff.2 fun i ↦ by
      filter_upwards [Lp.coeFn_smul (ℓ (0, Pi.single i 1)) (brownianLp hB i)] with w hw
      rw [hw, Pi.smul_apply, smul_eq_mul]
  filter_upwards [Lp.coeFn_add (ℓ (1, 0) • Z) (∑ i : I, ℓ (0, Pi.single i 1) • brownianLp hB i),
    Lp.coeFn_smul (ℓ (1, 0)) Z, hsum, hB', hsmul] with w h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, Finset.sum_apply]
  simp_rw [h5, h4]
  -- expand ℓ on the decomposition of the vector
  have hdec : spaceVector B Z I w =
      Z w • ((1 : ℝ), (0 : I → ℝ)) + ∑ i : I, B i w • ((0 : ℝ), Pi.single i (1 : ℝ)) := by
    ext x
    · simp only [spaceVector, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, Finset.univ_eq_attach, mul_zero,
        Prod.fst_add, Prod.fst_sum, Finset.sum_const_zero, add_zero]
    · simp only [spaceVector, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, Finset.univ_eq_attach, mul_zero,
        Prod.snd_add, Prod.snd_sum, Pi.add_apply, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite,
        Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte, zero_add]
  rw [hdec, map_add, map_smul, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine congrArg₂ (· + ·) (mul_comm _ _) (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)
theorem hasGaussianLaw_spaceVector (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) {Z : RandomL2 P} (hZ : Z ∈ Space P) (I : Finset ℝ≥0) :
    HasGaussianLaw (spaceVector B Z I) P := by
  refine ⟨isGaussian_of_isGaussian_map fun ℓ ↦ ?_⟩
  have hmeas := aemeasurable_spaceVector hB Z I
  rw [AEMeasurable.map_map_of_aemeasurable ℓ.continuous.measurable.aemeasurable hmeas]
  have hmem : ℓ (1, 0) • Z + ∑ i : I, ℓ (0, Pi.single i 1) • brownianLp hB i ∈ Space P :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hZ)
      (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (brownianLp_mem_space hB L hL i))
  have hG := (space_hasGaussianLaw P ⟨_, hmem⟩).congr (coeFn_combination_spaceVector hB Z I ℓ)
  exact hG.isGaussian_map
theorem covariance_coe_eval (hB : IsPreBrownianReal B P) {Z : RandomL2 P} (hZ : Z ∈ Space P)
    (t : ℝ≥0) : cov[(Z : W → ℝ), B t; P] = ⟪Z, brownianLp hB t⟫_ℝ := by
  rw [covariance_eq_sub (Lp.memLp Z) ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two),
    integral_coe_eq_zero P ⟨Z, hZ⟩, zero_mul, sub_zero, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_brownianLp hB t] with w hw
  rw [Pi.mul_apply, hw]
  simp only [mul_comm, RCLike.inner_apply, conj_trivial]
theorem indepFun_of_orthogonal (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) {Z : RandomL2 P} (hZ : Z ∈ Space P)
    (horth : ∀ t, ⟪Z, brownianLp hB t⟫_ℝ = 0) (I : Finset ℝ≥0) :
    IndepFun (Z : W → ℝ) (fun w ↦ fun i : I ↦ B i w) P := by
  refine (hasGaussianLaw_spaceVector hB L hL hZ I).indepFun_of_covariance_strongDual
    fun L₁ L₂ ↦ ?_
  have h1 : (L₁ ∘ fun w ↦ (Z : W → ℝ) w) = fun w ↦ L₁ 1 * (Z : W → ℝ) w := by
    funext w
    calc L₁ ((Z : W → ℝ) w) = L₁ ((Z : W → ℝ) w • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = (Z : W → ℝ) w • L₁ 1 := map_smul _ _ _
      _ = L₁ 1 * (Z : W → ℝ) w := by rw [smul_eq_mul, mul_comm]
  have h2 : (L₂ ∘ fun w ↦ fun i : I ↦ B i w) = fun w ↦ ∑ i : I, L₂ (Pi.single i 1) * B i w := by
    funext w
    rw [Function.comp_apply]
    have : (fun i : I ↦ B i w) = ∑ i : I, B i w • Pi.single i (1 : ℝ) := by
      funext x
      simp only [Finset.univ_eq_attach, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
    rw [this, map_sum]
    simp_rw [map_smul, smul_eq_mul, mul_comm]
  rw [h1, h2, covariance_const_mul_left, covariance_fun_sum_right
    (X := fun i : I ↦ fun w ↦ L₂ (Pi.single i 1) * B i w)
    (fun i ↦ ((hB.isGaussianProcess.hasGaussianLaw_eval i).memLp_two).const_mul _) (Lp.memLp Z)]
  simp only [covariance_const_mul_right, covariance_coe_eval hB hZ, horth, mul_zero,
    Finset.sum_const_zero]
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
  [BorelSpace W] [SecondCountableTopology W] in
/-- The sigma-algebra generated by finitely many Brownian coordinates is the comap of the
finite vector. -/
theorem comap_finset_eq (B : ℝ≥0 → W → ℝ) (I : Finset ℝ≥0) :
    MeasurableSpace.comap (fun w ↦ fun i : I ↦ B i w) MeasurableSpace.pi =
      ⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ) := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_congr fun i ↦ ?_
  rw [MeasurableSpace.comap_comp]
  rfl
theorem indep_comap_processMeasurableSpace (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) {Z : RandomL2 P} (hZ : Z ∈ Space P)
    (horth : ∀ t, ⟪Z, brownianLp hB t⟫_ℝ = 0) :
    Indep (processMeasurableSpace B) (MeasurableSpace.comap (Z : W → ℝ) (borel ℝ)) P := by
  have : IsProbabilityMeasure P := inferInstance
  have hfin : ∀ I : Finset ℝ≥0, Indep (⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ))
      (MeasurableSpace.comap (Z : W → ℝ) (borel ℝ)) P := fun I ↦ by
    rw [← comap_finset_eq]
    exact ((IndepFun_iff_Indep _ _ _).mp (indepFun_of_orthogonal hB L hL hZ horth I)).symm
  have hdir : Directed (· ≤ ·) fun I : Finset ℝ≥0 ↦
      ⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ) := by
    intro I J
    refine ⟨I ∪ J, ?_, ?_⟩
    · exact iSup_le fun i ↦ le_iSup_of_le ⟨i.1, Finset.mem_union_left _ i.2⟩ le_rfl
    · exact iSup_le fun i ↦ le_iSup_of_le ⟨i.1, Finset.mem_union_right _ i.2⟩ le_rfl
  have hmeas : ∀ t, Measurable (B t) := fun t ↦ by
    have : B t = fun w ↦ L t w := funext (hL t)
    rw [this]
    exact (L t).continuous.measurable
  have hle : ∀ I : Finset ℝ≥0,
      (⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ)) ≤ ‹MeasurableSpace W› :=
    fun I ↦ iSup_le fun i ↦ (hmeas i).comap_le
  have hZle : MeasurableSpace.comap (Z : W → ℝ) (borel ℝ) ≤ ‹MeasurableSpace W› :=
    (Lp.stronglyMeasurable Z).measurable.comap_le
  have h := indep_iSup_of_directed_le hfin hle hZle hdir
  have hproc : processMeasurableSpace B =
      ⨆ I : Finset ℝ≥0, ⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ) := by
    unfold processMeasurableSpace
    rw [iSup_eq_iSup_finset]
    exact iSup_congr fun I ↦ (iSup_subtype (p := (· ∈ I))
      (f := fun t ↦ MeasurableSpace.comap (B t) (borel ℝ))).symm ▸ rfl
  rw [hproc]
  exact h
theorem eq_zero_of_mem_space_of_orthogonal (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {Z : RandomL2 P} (hZ : Z ∈ Space P) (horth : ∀ t, ⟪Z, brownianLp hB t⟫_ℝ = 0) : Z = 0 := by
  have hind := indep_comap_processMeasurableSpace hB L hL hZ horth
  rw [hgen] at hind
  have hself : IndepFun (Z : W → ℝ) (Z : W → ℝ) P :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left hind (Lp.stronglyMeasurable Z).measurable.comap_le)
  have hsq := hself.integral_fun_mul_eq_mul_integral (Lp.aestronglyMeasurable Z)
    (Lp.aestronglyMeasurable Z)
  rw [integral_coe_eq_zero P ⟨Z, hZ⟩, mul_zero] at hsq
  have hinner : ⟪Z, Z⟫_ℝ = 0 := by
    rw [L2.inner_def, ← hsq]
    apply integral_congr_ae
    filter_upwards with w
    simp only [inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq, sq,
      abs_mul_abs_self]
  exact inner_self_eq_zero.mp hinner
instance instCompleteSpaceFirstChaos (hB : IsPreBrownianReal B P) : CompleteSpace (firstChaos hB) :=
  inferInstanceAs
    (CompleteSpace ((Submodule.span ℝ (Set.range (brownianLp hB))).topologicalClosure))
theorem space_eq_firstChaos (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) :
    Space P = firstChaos hB := by
  refine le_antisymm (fun Z hZ ↦ ?_) (firstChaos_le_space hB L hL)
  set K := firstChaos hB with hK
  have hproj : K.starProjection Z ∈ Space P :=
    firstChaos_le_space hB L hL (K.starProjection_apply_mem Z)
  have hmem : Z - K.starProjection Z ∈ Space P := Submodule.sub_mem _ hZ hproj
  have horth : ∀ t, ⟪Z - K.starProjection Z, brownianLp hB t⟫_ℝ = 0 := fun t ↦
    (Submodule.mem_orthogonal' K _).mp (K.sub_starProjection_mem_orthogonal Z) _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩))
  have h0 := eq_zero_of_mem_space_of_orthogonal hB L hL hgen hmem horth
  rw [sub_eq_zero] at h0
  rw [h0]
  exact K.starProjection_apply_mem Z
noncomputable def timeDerivative (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) :
    Lp (Space P) 2 P →ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  timeDerivativeOfEq hB (space_eq_firstChaos hB L hL hgen)
noncomputable def timeDerivativeEquiv (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) :
    Lp (Space P) 2 P ≃ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  ((compLpEquiv (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen))).trans
    (compLpEquiv (wienerIntegralEquiv hB).symm)).trans fubiniEquiv
variable (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- A bounded `C¹` function of finitely many Brownian coordinates is smooth bounded. -/
theorem isSmoothBounded_cylinder {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    IsSmoothBounded (fun w ↦ f (fun i ↦ B (t i) w)) := by
  have : (fun w ↦ f (fun i ↦ B (t i) w)) = fun w ↦ f (fun i ↦ L (t i) w) := by
    funext w
    simp only [hL]
  rw [this]
  exact IsSmoothBounded.cylindrical f hf hb hb' _
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` is square integrable. -/
theorem memLp_cylinderPartial {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) (i : Fin n) :
    MemLp (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) 2 P := by
  obtain ⟨C, hC⟩ := hb'
  have hcont : Continuous fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1) := by
    have : (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) =
        fun w ↦ fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i 1) := by
      funext w
      simp only [hL]
    rw [this]
    exact ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_pi fun j ↦ (L (t j)).continuous)).clm_apply continuous_const
  refine MemLp.of_bound hcont.aestronglyMeasurable (C * ‖(Pi.single i 1 : Fin n → ℝ)‖)
    (Filter.Eventually.of_forall fun w ↦ ?_)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
noncomputable def cylinderPartial {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) (i : Fin n) : Lp ℝ 2 P :=
  (memLp_cylinderPartial L hL f hf hb' t i).toLp _
end CameronMartin
end Malliavin


