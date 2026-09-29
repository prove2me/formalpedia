-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/682bc583-fdc5-53f5-b7a3-581ed69ff71b

import Mathlib
import Definitions.Def_AlgebraicCurve_LogDeRhamH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff

set_option autoImplicit false
open KaehlerDifferential

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ π : v.toValuationSubring, Irreducible π ∧
      v.dCoord = KaehlerDifferential.D K F (π : F) ∧
      (∀ (n : ℕ) (ω : Ω[F⁄K]), v.HasPoleOrderLE n ω ↔
        ∃ f : F, (π : F) ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord) ∧
      (∀ (n : ℕ) (g : F), v.FnPoleOrderLE n g ↔ (π : F) ^ n * g ∈ v.toValuationSubring) ∧
      (∀ (ω : Ω[F⁄K]) (a : K), v.HasLogResidue ω a ↔
        ∃ f : F, ω = f • v.dCoord ∧ v.HasValue ((π : F) * f) a) := by
  exact ⟨_, (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec, rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff (solution)
