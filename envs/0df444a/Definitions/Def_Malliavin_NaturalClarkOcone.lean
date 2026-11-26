-- Prove2me | Definitions.Def_Malliavin_NaturalClarkOcone
-- name    : Malliavin_NaturalClarkOcone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:43:06.980616+00:00
-- url     : https://prove2.me/theorems/75f76fef-08ed-581b-97fe-73be65f1220f
-- title:
--   Natural Clark Ocone
-- statement:
--   Definitions and structural lemmas for Natural Clark Ocone, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean

import Definitions.Def_Malliavin_KernelIdentification
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_isClosed_naturalItoRange
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
noncomputable def expectationL2CLM : RandomL2 P →L[ℝ] RandomL2 P :=
  (Lp.constL 2 P ℝ).comp (CameronMartin.expectationMap P)
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
@[simp]
theorem expectationL2CLM_apply (G : RandomL2 P) :
    expectationL2CLM G = expectationL2 G := by
  rw [expectationL2CLM, ContinuousLinearMap.comp_apply,
    CameronMartin.expectationMap_apply, expectationL2, Lp.constL_apply]
noncomputable def centeredPartCLM : RandomL2 P →L[ℝ] RandomL2 P :=
  ContinuousLinearMap.id ℝ (RandomL2 P) - expectationL2CLM
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
@[simp]
theorem centeredPartCLM_apply (G : RandomL2 P) :
    centeredPartCLM G = G - expectationL2 G := by
  rw [centeredPartCLM, sub_apply,
    ContinuousLinearMap.id_apply, expectationL2CLM_apply]
def SmoothNaturalClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ (G : W → ℝ) (hG : IsSmoothBounded G),
    hG.toLp P = expectationL2 (hG.toLp P) +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))
def SmoothNaturalItoDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ (G : W → ℝ) (hG : IsSmoothBounded G) (U : PredictableProcessL2 𝓅 P),
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P))) U
def SmoothElementaryNaturalItoDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ (G : W → ℝ) (hG : IsSmoothBounded G) (a b : ℝ≥0) (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓅 a) 2 P),
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))
        (elementaryPredictable 𝓅 a b Z)
noncomputable def pastCylinderLpMeas
    (_hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (t : Fin n → ℝ≥0) (a : ℝ≥0) (ht : ∀ i, t i ≤ a) :
    lpMeas ℝ ℝ (𝓅 a) 2 P := by
  let hZ := isSmoothBounded_cylinder coordinate coordinate_apply f hf hb hb' t
  refine ⟨hZ.toLp P, ?_⟩
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have hcoord (i : Fin n) : Measurable[𝓅 a] (B (t i)) := by
    apply measurable_iff_comap_le.mpr
    rw [hnat]
    exact le_iSup₂
      (f := fun (j : ℝ≥0) (_ : j ≤ a) ↦
        MeasurableSpace.comap (B j) inferInstance) (t i) (ht i)
  have hvec : Measurable[𝓅 a] (fun w ↦ fun i ↦ B (t i) w) :=
    by
      let _ : MeasurableSpace W := 𝓅 a
      exact measurable_pi_lambda _ hcoord
  have hZmeas : StronglyMeasurable[𝓅 a]
      (fun w ↦ f (fun i ↦ B (t i) w)) :=
    (hf.continuous.measurable.comp hvec).stronglyMeasurable
  exact hZmeas.aestronglyMeasurable.congr
    (MemLp.coeFn_toLp (hZ.memLp P 2)).symm
noncomputable def elementaryPredictableCoefficientCLM
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0) :
    lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  LinearMap.mkContinuous
    { toFun := elementaryPredictable 𝓕 a b
      map_add' := fun Z Y ↦ by
        apply Subtype.ext
        exact tensor_add (iocIndicator a b) (Z : RandomL2 P) (Y : RandomL2 P)
      map_smul' := fun c Z ↦ by
        apply Subtype.ext
        exact tensor_smul (iocIndicator a b) c (Z : RandomL2 P) }
    ‖iocIndicator a b‖ fun Z ↦ by
      change ‖tensor (iocIndicator a b) (Z : RandomL2 P)‖ ≤ ‖iocIndicator a b‖ * ‖Z‖
      rw [norm_tensor, Submodule.norm_coe]
noncomputable def elementaryBrownianCoefficientCLM
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (_hab : a ≤ b) :
    lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] RandomL2 P :=
  (naturalItoIntegral hB hsm hnat).comp
    (elementaryPredictableCoefficientCLM (P := P) 𝓕 a b)
def pastCylinderSet
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    Set (lpMeas ℝ ℝ (𝓕 a) 2 P) :=
  {Z | ∃ (n : ℕ) (f : (Fin n → ℝ) → ℝ)
      (hf : ContDiff ℝ 1 f)
      (hb : ∃ C, ∀ y, |f y| ≤ C)
      (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
      (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ a),
    Z = pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
      f hf hb hb' t a ht}
def pastCylinderSpan
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    Submodule ℝ (lpMeas ℝ ℝ (𝓕 a) 2 P) :=
  Submodule.span ℝ
    (pastCylinderSet hB coordinate coordinate_apply hsm hnat a)
def PastCylinderDense
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) : Prop :=
  ∀ a, Dense (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a :
    Set (lpMeas ℝ ℝ (𝓕 a) 2 P))
theorem naturalClarkOcone_of_smooth
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) :
    F.1 = expectationL2 F.1 +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) := by
  obtain ⟨G, hG, hDG⟩ := inGraphClosure_mderivClosure P F.2
  let R : Lp (CameronMartin.Space P) 2 P →L[ℝ] RandomL2 P :=
    (naturalItoIntegral hB hsm hnat).comp
      ((predictableProjection 𝓅).comp
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          ).toContinuousLinearMap)
  have heq (n : ℕ) :
      centeredPartCLM ((G n).2.toLp P) = R ((G n).2.mderivLp P) := by
    rw [centeredPartCLM_apply]
    have hc := hCore (G n).1 (G n).2
    calc
      (G n).2.toLp P - expectationL2 ((G n).2.toLp P) =
          (expectationL2 ((G n).2.toLp P) +
            naturalItoIntegral hB hsm hnat
              (predictableProjection 𝓅
                (Malliavin.timeDerivative hB coordinate coordinate_apply generated
                  ((G n).2.mderivLp P)))) -
            expectationL2 ((G n).2.toLp P) :=
        congrArg (fun X : RandomL2 P ↦
          X - expectationL2 ((G n).2.toLp P)) hc
      _ = naturalItoIntegral hB hsm hnat
          (predictableProjection 𝓅
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              ((G n).2.mderivLp P))) := by abel
  have hleft :
      Tendsto (fun n ↦ centeredPartCLM ((G n).2.toLp P)) atTop
        (𝓝 (centeredPartCLM F.1)) :=
    ((centeredPartCLM (P := P)).continuous.tendsto F.1).comp hG
  have hright :
      Tendsto (fun n ↦ R ((G n).2.mderivLp P)) atTop
        (𝓝 (R (mderivClosure P F.1))) :=
    (R.continuous.tendsto (mderivClosure P F.1)).comp hDG
  rw [show (fun n ↦ centeredPartCLM ((G n).2.toLp P)) =
      fun n ↦ R ((G n).2.mderivLp P) by
        funext n
        exact heq n] at hleft
  have hcenter : centeredPartCLM F.1 = R (mderivClosure P F.1) :=
    tendsto_nhds_unique hleft hright
  rw [centeredPartCLM_apply] at hcenter
  change F.1 - expectationL2 F.1 =
    naturalItoIntegral hB hsm hnat
      (predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) at hcenter
  calc
    F.1 = expectationL2 F.1 + (F.1 - expectationL2 F.1) := by abel
    _ = expectationL2 F.1 +
        naturalItoIntegral hB hsm hnat
          (predictableProjection 𝓅
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              (mderivD12 P F))) := by rw [hcenter]
theorem naturalMartingaleRepresentation_of_smoothClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  intro F
  have hmem : centeredPartCLM F ∈ naturalItoRange hB hsm hnat := by
    refine (denseRange_toLp P).induction_on F ?_ ?_
    · exact (isClosed_naturalItoRange hB hsm hnat).preimage
        (centeredPartCLM (P := P)).continuous
    · rintro ⟨G, hG⟩
      rw [centeredPartCLM_apply]
      let V := predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hG.mderivLp P))
      refine ⟨V, ?_⟩
      have hc := hCore G hG
      have hcenter : hG.toLp P - expectationL2 (hG.toLp P) =
          naturalItoIntegral hB hsm hnat V := by
        calc
          hG.toLp P - expectationL2 (hG.toLp P) =
              (expectationL2 (hG.toLp P) + naturalItoIntegral hB hsm hnat V) -
                expectationL2 (hG.toLp P) :=
            congrArg (fun X : RandomL2 P ↦ X - expectationL2 (hG.toLp P)) hc
          _ = naturalItoIntegral hB hsm hnat V := by abel
      exact hcenter.symm
  obtain ⟨U, hU⟩ := hmem
  refine ⟨U, ?_⟩
  rw [centeredPartCLM_apply] at hU
  change naturalItoIntegral hB hsm hnat U = F - expectationL2 F at hU
  calc
    F = expectationL2 F + (F - expectationL2 F) := by abel
    _ = expectationL2 F + naturalItoIntegral hB hsm hnat U := by rw [← hU]
theorem naturalItoDuality_of_smoothClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by
  let V := predictableProjection 𝓅
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (mderivD12 P F))
  have hCO := naturalClarkOcone_of_smooth hB coordinate coordinate_apply generated
    hsm hnat hCore F
  have hcenter : F.1 - expectationL2 F.1 =
      naturalItoIntegral hB hsm hnat V := by
    calc
      F.1 - expectationL2 F.1 =
          (expectationL2 F.1 + naturalItoIntegral hB hsm hnat V) -
            expectationL2 F.1 :=
        congrArg (fun X : RandomL2 P ↦ X - expectationL2 F.1) hCO
      _ = naturalItoIntegral hB hsm hnat V := by abel
  calc
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (naturalItoIntegral hB hsm hnat V)
          (naturalItoIntegral hB hsm hnat U) := by rw [hcenter]
    _ = inner ℝ V U := inner_naturalItoIntegral hB hsm hnat V U
noncomputable def ClarkOconeFamily.ofNaturalItoSmoothClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalIto hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_smoothClarkOcone
      hB coordinate coordinate_apply generated hsm hnat hCore)
    (naturalItoDuality_of_smoothClarkOcone
      hB coordinate coordinate_apply generated hsm hnat hCore)
end Malliavin
end


