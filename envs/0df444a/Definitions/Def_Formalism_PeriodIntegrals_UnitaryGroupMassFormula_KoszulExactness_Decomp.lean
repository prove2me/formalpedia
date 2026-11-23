-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:41.694809+00:00
-- url     : https://prove2.me/theorems/2f196582-be65-4911-9498-599dbc2cc627
-- title:
--   Decomp
-- statement:
--   Definitions and structural lemmas for Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
def Dc (R : Type u) [CommRing R] {D : ℕ} (i : Fin D) (p q : ℕ) (x : ExteriorAlgebra R (Fin D → R)) :
    Prop :=
  ∃ a ∈ Li R D i ^ p, ∃ b ∈ Li R D i ^ q, x = a + eb R i * b
end PI.KoszulExact


