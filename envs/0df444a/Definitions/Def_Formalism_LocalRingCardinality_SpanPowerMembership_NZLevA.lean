-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:32.636313+00:00
-- url     : https://prove2.me/theorems/ac11c7d8-5905-458c-8ef7-671a83f5643d
-- title:
--   NZLev A
-- statement:
--   Definitions and structural lemmas for NZLev A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevA.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ
variable {k : ℕ}
def tailL (L : Submodule W (Fin k → Q)) (c : ℕ) : Submodule W (Fin k → Q) where
  carrier := {y | y ∈ L ∧ ∀ i : Fin k, i.val < c → y i = 0}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨L.add_mem h1 h3, fun i hi => by rw [Pi.add_apply, h2 i hi, h4 i hi, add_zero]⟩
  zero_mem' := ⟨L.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro r a ⟨h1, h2⟩
    exact ⟨L.smul_mem r h1, fun i hi => by rw [Pi.smul_apply, h2 i hi, smul_zero]⟩
end Formalism.BasicNotions.Examples₂.NZ


