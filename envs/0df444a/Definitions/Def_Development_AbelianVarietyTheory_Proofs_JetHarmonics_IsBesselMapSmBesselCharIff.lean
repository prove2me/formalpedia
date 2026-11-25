-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBesselMapSmBesselCharIff
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBesselMapSmBesselCharIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:59:12.818815+00:00
-- url     : https://prove2.me/theorems/f97c35cd-b021-4b4f-9699-b9c2330c9446
-- title:
--   Is Bessel Map Sm Bessel Char Iff
-- statement:
--   Definitions and structural lemmas for Is Bessel Map Sm Bessel Char Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBesselMapSmBesselCharIff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.BesselMapCompare
open PI.UpqRep GlobalTheory.IndefiniteRowSideFullHecke
def scaleEquiv (r : ℕ) : (Fin r → ℂ) ≃ (Fin r → ℂ) where
  toFun κ := fun a => -2 * Complex.I * κ a
  invFun c := fun a => Complex.I / 2 * c a
  left_inv κ := by
    funext a
    linear_combination (-κ a) * Complex.I_mul_I
  right_inv c := by
    funext a
    linear_combination (-c a) * Complex.I_mul_I
section Maps
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end Maps
end GlobalTheory.BesselMapCompare
end


