-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:27.158285+00:00
-- url     : https://prove2.me/theorems/84c9ccb6-4509-4c79-9c1e-9b787e8f26dd
-- title:
--   Points
-- statement:
--   Definitions and structural lemmas for Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Points.lean

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
theorem mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ζ.asIdeal ∈ (maximalIdeal O).primesOver ↥(As O A) := by
  haveI := ζ.isMaximal
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal)).symm
theorem isMaximal_of_mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] {q : Ideal ↥(As O A)}
    (hq : q ∈ (maximalIdeal O).primesOver ↥(As O A)) : q.IsMaximal := by
  obtain ⟨hp, hl⟩ := hq
  have h : q.comap (algebraMap O ↥(As O A)) = maximalIdeal O := hl.over.symm
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q (h ▸ IsLocalRing.maximalIdeal.isMaximal O)
noncomputable def ptsEquiv (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] :
    Pts O A ≃ (maximalIdeal O).primesOver ↥(As O A) where
  toFun ζ := ⟨ζ.asIdeal, mem_primesOver O A ζ⟩
  invFun q := ⟨q.1, isMaximal_of_mem_primesOver O A q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end PI.UnitaryGroupMassFormula.EfRankSum


