-- Prove2me | solution 1 for AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7a32bdf8-d01e-576f-9016-583351942b44

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem isIntegrallyClosed_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {_} _ => ⟨0, Subsingleton.elim _ _⟩

theorem solution {X : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) := by
  by_cases hne : Nonempty U
  ·
    haveI := hne
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : U, hU.primeIdealOf x = y :=
      ⟨⟨hU.fromSpec.base y, hy⟩, hU.fromSpec.injective (by rw [hU.fromSpec_primeIdealOf])⟩
    haveI : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := by
      have := hU.isLocalization_stalk x
      rw [hx] at this
      exact this
    haveI := h x.1
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv
  ·
    have hU0 : U = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hne ⟨⟨z, hz⟩⟩
    subst hU0
    exact isIntegrallyClosed_of_subsingleton _

end S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk (solution)
