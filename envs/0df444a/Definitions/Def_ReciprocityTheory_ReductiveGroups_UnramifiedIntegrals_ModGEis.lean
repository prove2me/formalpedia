-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:27.547337+00:00
-- url     : https://prove2.me/theorems/9e1190c7-b5c9-4566-97c2-9e4a463f7817
-- title:
--   Mod GEis
-- statement:
--   Definitions and structural lemmas for Mod GEis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGEis.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩
end ReciprocityTheory.ChartRestriction.L1


