-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:26.566287+00:00
-- url     : https://prove2.me/theorems/9113c5dc-e3f7-4f35-91fa-8eee17d94e61
-- title:
--   Nat Mul Factorial Bound
-- statement:
--   Definitions and structural lemmas for Nat Mul Factorial Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI.DivPowInteg.Top
open PI.DivPowInteg.Gen
section
variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]
noncomputable def dpow (κ : I → J → K) (n : ℕ) (R : MvPolynomial (I ⊕ J) K) :
    MvPolynomial (I ⊕ J) K :=
  ((n.factorial : ℚ)⁻¹) • (gdelta κ ^ n) R
def Good (L : Submodule A K) (n : ℕ) (Q : MvPolynomial (I ⊕ J) K) : Prop :=
  ∀ m, Q.coeff m ∈ L ^ n
end
end PI.DivPowInteg.Top


