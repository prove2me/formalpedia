-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormFib
-- name    : ReciprocityTheory_L2DbarEstimates_NormFibrations_NormFib
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:52.997571+00:00
-- url     : https://prove2.me/theorems/088ec7ef-3a75-4342-a047-cda250c29e76
-- title:
--   Norm Fib
-- statement:
--   Definitions and structural lemmas for Norm Fib, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/NormFib.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.L2DbarEstimates
open Filter Topology
def NormFibStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ y : V n, (z ⁻¹' {y}).Finite) → ConnectedSpace M →
    ∃ δ : ℕ, ∀ y : V n, (z ⁻¹' {y}).encard ≤ δ
end ReciprocityTheory.L2DbarEstimates


