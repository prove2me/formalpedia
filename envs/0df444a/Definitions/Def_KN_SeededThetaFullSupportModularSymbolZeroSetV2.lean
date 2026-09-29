-- Prove2me | Definitions.Def_KN_SeededThetaFullSupportModularSymbolZeroSetV2
-- name    : KN_SeededThetaFullSupportModularSymbolZeroSetV2
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:21:28.340933+00:00
-- url     : https://prove2.me/theorems/8e278eb4-abc1-4e77-910b-f95e2a465213
-- title:
--   Full-support modular-symbol zero sets over rebased data
-- statement:
--   The full-support modular-symbol zero-set predicate for seeded finite theta data, rebuilt over the rebased full-support interpolation definitions.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededThetaFullSupportInterpolationV3

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- At characters which are primitive at the full selected support, evaluation
of the finite theta element has the same zero set as the complex modular-symbol
sum occurring in the Birch--Mellin formula for the product of the seed and the
realized horizontal character.  This isolates the finite theta construction
from the analytic Birch--Mellin calculation. -/
def SeededFiniteThetaDataV3.HasFullSupportModularSymbolZeroSet
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ χ, (Θ.characters.realized χ).2.conductor = L.supportModulus χ.support →
    (Θ.eval χ ≠ 0 ↔
      let θ := primitiveProductV2 η (Θ.characters.realized χ)
      letI : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form (k / 2 - 1) a.val θ.1.1) ≠ 0)

end HorizontalPadicL


