-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:22.981958+00:00
-- url     : https://prove2.me/theorems/617c3f87-41a1-4db7-88c2-4313857ee2b0
-- title:
--   Index St
-- statement:
--   Definitions and structural lemmas for Index St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/IndexSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
def IndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subring K),
    Module.Free ℤ O → Module.Finite ℤ O → Module.finrank ℤ O = Module.finrank ℚ K →
    ∀ f : O, f ≠ 0 →
      (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| ∧
      Real.log (Nat.card (O ⧸ Ideal.span {f})) = ∑ σ : K →+* ℂ, Real.log ‖σ f‖
end ReciprocityTheory.ChartRestriction.G.AI


