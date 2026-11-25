-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_GoodRingWittExtension
-- name    : Formalism_LocalToGlobal_GroupLattices_PerfectRings_GoodRingWittExtension
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:03.801305+00:00
-- url     : https://prove2.me/theorems/5525d906-57dd-4edc-802b-6525377a1e89
-- title:
--   Good Ring Witt Extension
-- statement:
--   Definitions and structural lemmas for Good Ring Witt Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/GoodRingWittExtension.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_G_settingStd
import Theorems.Thm_Formalism_L2_G_wU_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
namespace Formalism.L2.G
open Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
def dvrOO (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) : UniformizedDVR p (OO p n) :=
  dvrOfStd (settingStd p n h5 h2 he)
def resF : F1 p n →+* FF (OO p n) :=
  (Ideal.Quotient.lift (Ideal.span {(p : WQ p n)})
      ((IsLocalRing.residue (OO p n)).comp (jO p n)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, map_mul, map_natCast, ← wU_sq, map_pow]
    have : IsLocalRing.residue (OO p n) (wU p n) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact (Formalism.BasicNotions.Examples₂.GatR.om_irreducible (WittVector.irreducible p)).not_isUnit
    rw [this]; simp)).comp
    (WittVector.quotientPEquiv (p := p) (k := F1 p n)).symm.toRingHom
end Formalism.L2.G


