-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:49.808538+00:00
-- url     : https://prove2.me/theorems/771c3f04-cf84-436e-95f2-efe3a6e8ad59
-- title:
--   Row Col A
-- statement:
--   Definitions and structural lemmas for Row Col A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
section Ring
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
def capT {p : ℕ} (R C : Fin (p + 1) → Fin n) (y : ℂ) (s j : Fin (p + 1)) : 𝒰 :=
  if R s = C j then ((-1 : ℂ) ^ ((s : ℕ) + (j : ℕ) + 1)) • cminor E (R ∘ s.succAbove) (C ∘ j.succAbove) y
  else 0
end Ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli


