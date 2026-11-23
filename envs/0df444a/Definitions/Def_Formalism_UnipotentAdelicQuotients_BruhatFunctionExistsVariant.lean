-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_BruhatFunctionExistsVariant
-- name    : Formalism_UnipotentAdelicQuotients_BruhatFunctionExistsVariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:46.217344+00:00
-- url     : https://prove2.me/theorems/e78e74ef-f488-4483-830d-33ea5dbd23a4
-- title:
--   Bruhat Function Exists Variant
-- statement:
--   Definitions and structural lemmas for Bruhat Function Exists Variant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/BruhatFunctionExistsVariant.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace HeckeCharacterZeroLocus
open MeasureTheory Pointwise
def BruhatFunctionExistsVariant : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure H), μ.IsHaarMeasure →
      ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
        (∀ K : Set G, IsCompact K → IsCompact (tsupport β ∩ (K * (H : Set G)))) ∧
        ∀ x : G, ∫ h : H, β (x * (h : G)) ∂μ = 1
end HeckeCharacterZeroLocus


