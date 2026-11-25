-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofUMapSqSmul
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofUMapSqSmul
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:10:35.998625+00:00
-- url     : https://prove2.me/theorems/bb61eeb0-c28c-5307-8566-2d641a21adb3
-- title:
--   Tof UMap Sq Smul
-- statement:
--   Definitions and structural lemmas for Tof UMap Sq Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofUMapSqSmul.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def PerFactor {X : PT E} {DF : ℕ} (P : Par X DF) (I : Submodule ℤ (Vsp X.dim))
    (s : (Fin 1 → Vsp X.dim) → ℂ) : Prop :=
  ∀ w : Vsp X.dim, ∃ y ∈ X.L, Real.sqrt (X.ptN2 1 s fun _ => w) / Real.sqrt (X.l2 1 s) ≤
    Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y‖ ^ 2)
end
end ReciprocityTheory.ChartRestriction.G.I2


