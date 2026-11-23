-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:20.270145+00:00
-- url     : https://prove2.me/theorems/27b145dd-a3e4-4d9f-9fa1-a158f5f5e6a4
-- title:
--   Simple
-- statement:
--   Definitions and structural lemmas for Simple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
namespace PI.GreenLabelSurjWork
variable {G : Type} [Group G] [Fintype G]
def repHomLin (A B : Rep ℂ G) : (A ⟶ B) ≃ₗ[ℂ] A.ρ.IntertwiningMap B.ρ :=
  { Rep.homEquiv with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
end PI.GreenLabelSurjWork


