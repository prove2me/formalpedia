-- Prove2me | Definitions.Def_Malliavin_NaturalItoDuality
-- name    : Malliavin_NaturalItoDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:36:03.304961+00:00
-- url     : https://prove2.me/theorems/f35cc69d-b251-5147-a905-2314c75d32d3
-- title:
--   Natural Ito Duality
-- statement:
--   Definitions and structural lemmas for Natural Ito Duality, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_centeredNaturalItoIntegral_bestNaturalItoIntegrand

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
theorem naturalItoDuality_iff_bestNaturalItoIntegrand_eq_predictableProjection
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (F : D12 P) :
    (∀ U : PredictableProcessL2 𝓅 P,
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (predictableProjection 𝓅
          (timeDerivative hB L hL hgen (mderivD12 P F))) U) ↔
      bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (timeDerivative hB L hL hgen (mderivD12 P F)) := by
  let V := predictableProjection 𝓅
    (timeDerivative hB L hL hgen (mderivD12 P F))
  let Uₑ := bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1)
  have hcenter : naturalItoIntegral hB hsm hnat Uₑ =
      F.1 - expectationL2 F.1 := by
    have h := centeredNaturalItoIntegral_bestNaturalItoIntegrand
      hB hsm hnat hMRT (centeredPartL2 F.1)
    exact congrArg Subtype.val h
  constructor
  · intro hDuality
    apply ext_inner_right ℝ
    intro U
    calc
      inner ℝ Uₑ U =
          inner ℝ (naturalItoIntegral hB hsm hnat Uₑ)
            (naturalItoIntegral hB hsm hnat U) :=
        (inner_naturalItoIntegral hB hsm hnat Uₑ U).symm
      _ = inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) := by rw [hcenter]
      _ = inner ℝ V U := hDuality U
  · intro hbest U
    change Uₑ = V at hbest
    calc
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
          inner ℝ (naturalItoIntegral hB hsm hnat Uₑ)
            (naturalItoIntegral hB hsm hnat U) := by rw [hcenter]
      _ = inner ℝ Uₑ U := inner_naturalItoIntegral hB hsm hnat Uₑ U
      _ = inner ℝ V U := by rw [hbest]
noncomputable def ClarkOconeFamily.ofNaturalItoBestIntegrand
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (hBest : ∀ F : D12 P,
      bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
    hB coordinate coordinate_apply generated hsm hnat hMRT fun F U ↦
      (naturalItoDuality_iff_bestNaturalItoIntegrand_eq_predictableProjection
        hB coordinate coordinate_apply generated hsm hnat hMRT F).mpr (hBest F) U
end Malliavin


