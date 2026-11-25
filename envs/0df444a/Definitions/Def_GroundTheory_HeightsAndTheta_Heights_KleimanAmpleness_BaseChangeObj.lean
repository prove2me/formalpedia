-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:45.630662+00:00
-- url     : https://prove2.me/theorems/a2b31bc0-760f-4324-9c88-06cc0b35c4ae
-- title:
--   Base Change Obj
-- statement:
--   Definitions and structural lemmas for Base Change Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeObj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u u' w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def SubSystem.baseChange (O : Type u') [CommRing O] [Algebra O Ω] (Q : SubSystem S x Ω) : SubSystem O x Ω where
  sub I := Submodule.span (chartRing O x I) (Q.sub I : Set Ω)
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction
      (p := fun z _ => z ∈ Submodule.span (chartRing O x I₂) (Q.sub I₂ : Set Ω)) ?_ ?_ ?_ ?_ hz
    · intro z hz; exact Submodule.subset_span (Q.mono I₁ I₂ h z hz)
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz
end
end GroundTheory.Heights₂.Heights.Kleiman


