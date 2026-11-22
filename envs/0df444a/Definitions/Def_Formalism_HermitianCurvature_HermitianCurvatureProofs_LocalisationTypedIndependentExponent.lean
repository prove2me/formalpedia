-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:03.584893+00:00
-- url     : https://prove2.me/theorems/7610b2f5-f640-4c94-b678-f5dadf5c2ca9
-- title:
--   Localisation Typed Independent Exponent
-- statement:
--   Definitions and structural lemmas for Localisation Typed Independent Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
section LG
variable {E}
def ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : Ideal (𝓞 (maximalRealSubfield E)) where
  carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show algebraMap _ E (a + b) * t ∈ L
    rw [map_add, add_mul]; exact L.add_mem ha hb
  smul_mem' := fun c a ha => by
    show algebraMap _ E (c • a) * t ∈ L
    rw [smul_eq_mul, map_mul, mul_assoc]; exact hL.1 c _ ha
end LG
end Formalism.FourierDecayAlt.P.S6x6
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6
end Formalism.FourierDecayAlt.P


