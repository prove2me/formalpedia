-- Prove2me | Definitions.Def_Malliavin_ChaosMartingaleRepresentation
-- name    : Malliavin_ChaosMartingaleRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:52:41.119802+00:00
-- url     : https://prove2.me/theorems/7b2d61bc-fbda-46d0-818f-4905b066c924
-- title:
--   Chaos Martingale Representation
-- statement:
--   Definitions and structural lemmas for Chaos Martingale Representation, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChaosMartingaleRepresentation.lean

import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_homogeneousChaos_total
import Theorems.Thm_Malliavin_homogeneousChaos_zero_eq_constants
import Theorems.Thm_Malliavin_integral_multipleIntegralCLM
import Theorems.Thm_Malliavin_isClosed_naturalItoRange
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_naturalItoDuality_of_smooth
import Theorems.Thm_Malliavin_smoothNaturalItoDuality_of_elementary
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
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
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
omit [CompleteSpace W] [BorelSpace W] in
/-- If every positive selected homogeneous chaos is represented by a natural Itô terminal
value, then the natural Itô integral has the martingale-representation property. -/
theorem naturalMartingaleRepresentation_of_positiveChaos_le_naturalItoRange
    (hB : IsPreBrownianReal B P) (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  let K : Submodule ℝ (RandomL2 P) :=
    (naturalItoRange hB hsm hnat).comap
      (centeredPartCLM (P := P)).toLinearMap
  have hKclosed : IsClosed (K : Set (RandomL2 P)) := by
    exact (isClosed_naturalItoRange hB hsm hnat).preimage
      (centeredPartCLM (P := P)).continuous
  have hconstant : constantRandomVariables P ≤
      (centeredPartCLM (P := P)).ker := by
    unfold constantRandomVariables
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker]
      change centeredPartCLM ((Lp.constL 2 P ℝ) c) = 0
      rw [centeredPartCLM_apply, expectationL2]
      have hconst : ∫ w, (Lp.const 2 P c) w ∂P = c := by
        rw [integral_congr_ae (Lp.coeFn_const 2 P c)]
        simp
      rw [Lp.constL_apply, hconst, sub_self]
    · exact (centeredPartCLM (P := P)).isClosed_ker
  have hzero :
      (homogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) ≤ K := by
    intro F hF
    change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
    have hFconst : F ∈ constantRandomVariables P := by
      rw [← homogeneousChaos_zero_eq_constants hB]
      exact hF
    rw [show centeredPartCLM F = 0 by exact hconstant hFconst]
    exact zero_mem _
  have hpositiveCentered (n : ℕ) (hn : 0 < n) :
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤ K := by
    intro F hF
    change centeredPartCLM F ∈ naturalItoRange hB hsm hnat
    have hcentered : CameronMartin.expectationMap P F = 0 := by
      have hle : (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
          (CameronMartin.expectationMap P).ker := by
        unfold homogeneousChaos
        apply Submodule.topologicalClosure_minimal
        · rintro _ ⟨f, rfl⟩
          rw [LinearMap.mem_ker]
          change CameronMartin.expectationMap P (multipleIntegralCLM hB n f) = 0
          rw [CameronMartin.expectationMap_apply]
          exact integral_multipleIntegralCLM hB hn f
        · exact (CameronMartin.expectationMap P).isClosed_ker
      exact hle hF
    have hexpect : expectationL2 F = 0 := by
      rw [expectationL2, ← CameronMartin.expectationMap_apply, hcentered]
      exact map_zero _
    rw [centeredPartCLM_apply, hexpect, sub_zero]
    exact hpositive n hn hF
  have hchaos (n : ℕ) :
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤ K := by
    cases n with
    | zero => exact hzero
    | succ n => exact hpositiveCentered (n + 1) (Nat.zero_lt_succ n)
  have htop : (⊤ : Submodule ℝ (RandomL2 P)) ≤ K := by
    rw [← homogeneousChaos_total hB generated]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hchaos) hKclosed
  intro F
  have hmem : centeredPartCLM F ∈ naturalItoRange hB hsm hnat := by
    exact htop (Submodule.mem_top : F ∈ (⊤ : Submodule ℝ (RandomL2 P)))
  obtain ⟨U, hU⟩ := hmem
  refine ⟨U, ?_⟩
  rw [centeredPartCLM_apply] at hU
  change naturalItoIntegral hB hsm hnat U = F - expectationL2 F at hU
  calc
    F = expectationL2 F + (F - expectationL2 F) := by abel
    _ = expectationL2 F + naturalItoIntegral hB hsm hnat U := by rw [← hU]
noncomputable def ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hDuality : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalIto hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_positiveChaos_le_naturalItoRange
      hB generated hsm hnat hpositive)
    (naturalItoDuality_of_smooth
      hB coordinate coordinate_apply generated hsm hnat hDuality)
noncomputable def ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothElementaryDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hElementary : SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
    hB coordinate coordinate_apply generated hsm hnat hpositive
      (smoothNaturalItoDuality_of_elementary
        hB coordinate coordinate_apply generated hsm hnat hElementary)
end Malliavin
end


