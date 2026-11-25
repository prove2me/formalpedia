-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:23.095907+00:00
-- url     : https://prove2.me/theorems/25c74dbd-5a67-48e0-b4ce-4cc622c8a480
-- title:
--   Fg Of Unif Discrete
-- statement:
--   Definitions and structural lemmas for Fg Of Unif Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
section FG
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
noncomputable def coordMap : V →+ ((K →+* ℂ) → Fin (Module.finrank K V) → ℂ) where
  toFun v σ i := σ ((Module.finBasis K V).repr v i)
  map_zero' := by ext; simp
  map_add' v w := by ext; simp
end FG
end PI.UnitaryGroupMassFormula.TBDisc


