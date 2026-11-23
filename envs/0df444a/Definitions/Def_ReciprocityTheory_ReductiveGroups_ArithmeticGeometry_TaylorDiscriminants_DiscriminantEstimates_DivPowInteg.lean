-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:50.075698+00:00
-- url     : https://prove2.me/theorems/da7de81b-cc86-42ac-b970-7e68fb66c42e
-- title:
--   Div Pow Integ
-- statement:
--   Definitions and structural lemmas for Div Pow Integ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DivPowInteg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI
namespace DivPowInteg
noncomputable def delta {K I J : Type} [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) :
    MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)
end DivPowInteg
def DivPowInteg : Prop :=
  ∀ (A K I J : Type) [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
    [Fintype I] [Fintype J] (L : Submodule A K) (κ : I → J → K),
    (∀ i j, κ i j ∈ L) →
    ∀ (P : MvPolynomial (I ⊕ J) A) (n : ℕ),
      (∀ m, (((n.factorial : ℚ)⁻¹ •
          (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P)).coeff m) ∈ L ^ n) ∧
      (((∀ m ∈ P.support, ∑ i, m (Sum.inl i) < n) ∨ (∀ m ∈ P.support, ∑ j, m (Sum.inr j) < n)) →
        (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P) = 0)
end PI


