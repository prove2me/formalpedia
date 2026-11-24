-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:05.3108+00:00
-- url     : https://prove2.me/theorems/cd7f1b2f-73e8-4664-a975-5dade08e11f8
-- title:
--   Length Localized Module Quotient
-- statement:
--   Definitions and structural lemmas for Length Localized Module Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ObjectsChow
namespace VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
def eb (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, i⟩
    rfl
abbrev ι : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm
def Ψ (n : ℕ) : MRing (PBlk n) ≃+* MvPolynomial (Fin n) (𝓞 ℚ) :=
  (renameEquiv ℤ (eb n)).symm.toRingEquiv.trans (mapEquiv (Fin n) ι)
end VerticalPartMultiplicity
end ObjectsChow
end GroundTheory.Heights₂.Heights


