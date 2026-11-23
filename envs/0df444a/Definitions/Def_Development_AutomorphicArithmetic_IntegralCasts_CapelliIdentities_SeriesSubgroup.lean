-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:18.244691+00:00
-- url     : https://prove2.me/theorems/37d8424a-fae6-41f8-843d-94e5064b7252
-- title:
--   Series Subgroup
-- statement:
--   Definitions and structural lemmas for Series Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SeriesSubgroup.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvOfUnitCoeffMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FormalGroupCoeffMem
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
namespace UpperTheory.Reformulated.B.SeriesSubgroup
def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rwa [norm_neg]
def ser {R : Type} [CommRing R] (S : Subring R) : Subring R⟦X⟧ where
  carrier := {f | ∀ n, coeff n f ∈ S}
  mul_mem' := fun {a b} ha hb n => by
    rw [coeff_mul]
    exact S.sum_mem fun p _ => S.mul_mem (ha _) (hb _)
  one_mem' := fun n => by
    rw [coeff_one]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  add_mem' := fun {a b} ha hb n => by
    rw [map_add]
    exact S.add_mem (ha n) (hb n)
  zero_mem' := fun n => by
    rw [map_zero]
    exact S.zero_mem
  neg_mem' := fun {a} ha n => by
    rw [map_neg]
    exact S.neg_mem (ha n)
end UpperTheory.Reformulated.B.SeriesSubgroup


