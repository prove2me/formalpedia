-- Prove2me | Definitions.Def_KN_SeededThetaFullSupportInterpolationV3
-- name    : KN_SeededThetaFullSupportInterpolationV3
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:20:25.135982+00:00
-- url     : https://prove2.me/theorems/f12cf469-14b6-4837-81b6-94fa5f772e3d
-- title:
--   Full-support interpolation over the rebased inverse-seed convention
-- statement:
--   The full-support critical zero-set predicate for seeded finite theta data, rebuilt over `KN_InverseSeedConventionV2`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The finite theta element has the expected critical-value zero set for
horizontal characters whose primitive conductor uses every prime in their
chosen support.  Characters with redundant support are treated separately by
the horizontal norm relations. -/
def SeededFiniteThetaDataV3.HasFullSupportCriticalZeroSetV2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ χ, (Θ.characters.realized χ).2.conductor = L.supportModulus χ.support →
    (Θ.eval χ ≠ 0 ↔
      let θ := primitiveProductV2 η (Θ.characters.realized χ)
      @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
        (k / 2 - 1) ≠ 0)

end HorizontalPadicL


