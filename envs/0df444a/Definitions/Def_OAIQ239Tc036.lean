-- Prove2me | Definitions.Def_OAIQ239Tc036
-- name    : OAIQ239Tc036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:38.800287+00:00
-- url     : https://prove2.me/theorems/a29f5907-4f1c-4032-a1ac-2f5b5cf1c3f0
-- title:
--   Definitions bundle OAIQ239Tc036 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_Hodge_HodgeScalarRaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScalarRaw.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundle `OAIQ239Tc028` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc030` and `OAIQ239Tc031`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarRaw
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_raw_square_energy_smooth (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) (w : PreL2 A J α hs ht true) :
    (ComplexMatrix.square EuclideanEnergy.e a b ρ (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht w))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht w),hodgeWeakDerivative A J α hs ht
        (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
          (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  rw [hodgeRawDistribution_smooth,square_component_apply,hodge_smooth_energy_pair]
  congr 1
  apply chart_energy_local J α hs ht p.val (D p).toData A w.property hU hUD
    a b ρ ha hb hρ
    (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
      (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p w))
    (componentTest j φ) ?_ (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans hφU)
  intro z hz
  exact cutoff_realVector_raw A J α ht (fun q => (D q).toData) hD p w τ (hUD hz) (hτ z hz)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


