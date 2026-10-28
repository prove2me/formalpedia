-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:30:57.885994+00:00
-- url     : https://prove2.me/theorems/72f5f80b-8a06-4b88-9c28-6818c4e64bc7
-- title:
--   Weighted gradient operator for full-dimensional log-concave laws
-- statement:
--   For a log-concave probability law ν whose support has nonempty interior, `LogConcave.absolutelyContinuous_haar` gives absolute continuity with respect to any additive Haar measure, `frontier_support_eq_zero` gives ν-nullity of the support frontier, and `locallyDominates` gives local domination on compact subsets of the support interior. `weightedOperator` is the weighted-gradient operator built from this absolute continuity. The declarations `weightedOperator_isClosable` and `dense_domain_weightedOperator` state that this operator is closable and densely defined, and `closure_domRestrict_eq_of_smoothCore_le` gives the same closure for every core lying between the smooth core and the operator domain. No Poincaré inequality or KLS bound is asserted.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.WeightedGradient.Closable
--   import FunctionalInequalities.Energy.WeightedGradient.Core
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev weightedOperator (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) :
--       Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
--     Energy.WeightedGradient.operator ν B (hν.absolutelyContinuous_haar m hi)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/WeightedGradient/Closable`](https://prove2.me/theorems/fa58e2ea-ffc7-4bbc-a6b9-318f0f549a06), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`KLS/LogConcave/Density/BorellRepresentation/Construction`](https://prove2.me/theorems/533a10b6-a945-4efc-bb81-9cda52d67d80).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Basic.lean) · `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Basic.lean#L50-L119 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.Euclidean Probability
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
omit [CompleteSpace V] in
/-- A full-dimensional log-concave law is absolutely continuous with respect to Haar measure. -/
theorem absolutelyContinuous_haar (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) : (ν : Measure V) ≪ m :=
  hν.absolutelyContinuous_of_interior_support_nonempty m hi
omit [CompleteSpace V] in
/-- The frontier of the convex support of a full-dimensional log-concave law is null. -/
theorem frontier_support_eq_zero (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (ν : Measure V) (frontier (ν : Measure V).support) = 0 :=
  hν.absolutelyContinuous_haar Measure.addHaar hi
    (hν.convex_support.addHaar_frontier Measure.addHaar)
omit [CompleteSpace V] in
/-- On compact subsets of the support interior the Borell density is bounded below by a positive
constant, so Haar measure is locally dominated by the law. -/
theorem locallyDominates (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) : LocallyDominates ν m := by
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m hi
    (hν.absolutelyContinuous_haar m hi)
  intro K hK hKΩ
  obtain ⟨a, b, ha, hab⟩ := hρ.exists_bounds_of_isCompact hK hKΩ
  set a' : ℝ≥0 := Real.toNNReal a with ha'
  have ha'0 : a' ≠ 0 := (Real.toNNReal_pos.mpr ha).ne'
  refine ⟨a'⁻¹, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs, smul_eq_mul,
    ENNReal.coe_inv ha'0]
  have hν' : (ν : Measure V) (s ∩ K) = ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ∂m := by
    rw [← hρ.withDensity_eq, withDensity_apply _ (hs.inter hK.measurableSet)]
  have hlow : (a' : ℝ≥0∞) * m (s ∩ K) ≤ (ν : Measure V) (s ∩ K) := by
    rw [hν', ← setLIntegral_const]
    refine setLIntegral_mono hρ.measurable.ennreal_ofReal fun x hx ↦ ?_
    exact ENNReal.ofReal_le_ofReal (hab x hx.2).1
  have ha'top : (a' : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have ha'0' : (a' : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha'0
  calc m (s ∩ K) = ((a' : ℝ≥0∞))⁻¹ * ((a' : ℝ≥0∞) * m (s ∩ K)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha'0' ha'top, one_mul]
    _ ≤ ((a' : ℝ≥0∞))⁻¹ * (ν : Measure V) (s ∩ K) := by gcongr
variable (B : V →L[ℝ] V)
/-- The weighted gradient operator of a full-dimensional log-concave law. -/
abbrev weightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  Energy.WeightedGradient.operator ν B (hν.absolutelyContinuous_haar m hi)
/-- Closability on a full-dimensional log-concave law. -/
theorem weightedOperator_isClosable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.weightedOperator m B hi).IsClosable :=
  Energy.WeightedGradient.operator_isClosable ν B _ (hν.frontier_support_eq_zero hi)
    (hν.locallyDominates m hi)
/-- Dense domain on a full-dimensional log-concave law. -/
theorem dense_domain_weightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.weightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  Energy.WeightedGradient.dense_domain_operator ν B _
/-- Every core between the smooth compactly supported classes and the full domain has the same
closure as the operator; the Blueprint's `ℝ + C_c^∞(V)` is such a core. -/
theorem closure_domRestrict_eq_of_smoothCore_le (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    {S : Submodule ℝ (Lp ℝ 2 (ν : Measure V))} (hS : Energy.WeightedGradient.smoothCore ν ≤ S)
    (hS' : S ≤ (hν.weightedOperator m B hi).domain) :
    ((hν.weightedOperator m B hi).domRestrict S).closure = (hν.weightedOperator m B hi).closure :=
  Energy.WeightedGradient.closure_domRestrict_eq_of_smoothCore_le ν B _
    (hν.frontier_support_eq_zero hi) (hν.weightedOperator_isClosable m B hi) hS hS'
end FullDimensional
end LogConcave
end KLS
end FunctionalInequalities


