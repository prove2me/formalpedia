-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
-- name    : ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:05.281916+00:00
-- url     : https://prove2.me/theorems/2af34d4b-5972-4587-99b6-20d1d96cfb79
-- title:
--   Hom Dens A
-- statement:
--   Definitions and structural lemmas for Hom Dens A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
def cf {α β : Type*} (n : ℕ) (P : Matrix α β ℂ[X]) : Matrix α β ℂ := P.map fun p => p.coeff n
end
end ReciprocityTheory.AnForm.P


