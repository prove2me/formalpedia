-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:49.333752+00:00
-- url     : https://prove2.me/theorems/f65d0639-8a65-4961-b391-5cf0d846fe8d
-- title:
--   Basis Extend
-- statement:
--   Definitions and structural lemmas for Basis Extend, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BasisExtend.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LinearIndependentC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}
noncomputable def liftY : FractionRing (MvPolynomial σ L) →+* FractionRing (MvPolynomial σ E) :=
  IsFractionRing.lift (A := MvPolynomial σ L)
    (g := (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map (algebraMap L E)))
    ((IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map_injective _ (algebraMap L E).injective))
end ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension


