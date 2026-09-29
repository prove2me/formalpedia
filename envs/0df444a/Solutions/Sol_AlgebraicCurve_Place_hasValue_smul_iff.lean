-- Prove2me | solution 1 for AlgebraicCurve.Place.hasValue_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/dfa8254c-f527-5eca-aeae-900fb80b6927

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_hasValue_smul_iff

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (g : F) (a : K) :
    (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by

  have one : ∀ (τ : F ≃ₐ[K] F) (w : Place K F) (x : F), w.HasValue x a → (τ • w).HasValue (τ x) a := by
    intro τ w x ⟨hx, hres⟩
    let e := Place.smulRingEquiv τ w.toValuationSubring
    have hmem : τ x ∈ (τ • w).toValuationSubring := (e ⟨x, hx⟩).2
    refine ⟨hmem, ?_⟩
    have hex : (⟨τ x, hmem⟩ : (τ • w).toValuationSubring) = e ⟨x, hx⟩ := Subtype.ext rfl
    have key : (Place.smulResidueAlgEquiv τ w) (residue w.toValuationSubring ⟨x, hx⟩)
        = residue (τ • w).toValuationSubring (e ⟨x, hx⟩) := by
      show IsLocalRing.ResidueField.mapEquiv _ (residue _ _) = residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    rw [hex, ← key, hres, AlgEquiv.commutes]
  refine ⟨fun h => ?_, one σ v g⟩
  have := one σ⁻¹ (σ • v) (σ g) h
  rwa [inv_smul_smul, show σ⁻¹ (σ g) = g from σ.symm_apply_apply g] at this

end S_AlgebraicCurve_Place_hasValue_smul_iff
end P2MW
export P2MW.S_AlgebraicCurve_Place_hasValue_smul_iff (solution)
