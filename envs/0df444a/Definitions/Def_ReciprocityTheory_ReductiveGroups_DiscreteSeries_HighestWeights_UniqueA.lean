-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:14.600807+00:00
-- url     : https://prove2.me/theorems/6055e0a1-12df-40fe-88a9-e89184616ec4
-- title:
--   Unique A
-- statement:
--   Definitions and structural lemmas for Unique A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
section
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
end
section
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
def uqG (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n) :
    Module.End ℂ (WithLp 2 (V × V')) :=
  LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm
    (LinearMap.prodMapRingHom ℂ V V' (F a b, F' a b))
end
section
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
end
end ReciprocityTheory.ChartRestriction.DS.HW


