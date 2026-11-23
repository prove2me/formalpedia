-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DetAlg
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DetAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:29.137095+00:00
-- url     : https://prove2.me/theorems/504877b6-c4f2-43f5-b6b7-be38e40ac3c9
-- title:
--   Det Alg
-- statement:
--   Definitions and structural lemmas for Det Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DetAlg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.TB
def DetAlgSt : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K)), I.IsRadical →
    ∀ r : MvPolynomial (Fin n) K ⧸ I,
      (∀ (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
        (φ : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] L), φ r = 0) → r = 0
example : (⊥ : Ideal (MvPolynomial (Fin 0) ℚ)).IsRadical := Ideal.isRadical_bot
end ReciprocityTheory.ChartRestriction.G.TB


