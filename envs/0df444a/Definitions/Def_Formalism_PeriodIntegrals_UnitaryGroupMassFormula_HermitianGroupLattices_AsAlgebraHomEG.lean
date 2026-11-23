-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:53.717951+00:00
-- url     : https://prove2.me/theorems/8f7429c8-d685-47ab-b9e4-f913e687cc76
-- title:
--   As Algebra Hom EG
-- statement:
--   Definitions and structural lemmas for As Algebra Hom EG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/AsAlgebraHomEG.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.GLatHermW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
def cf (T : GoodSet K G) (g : G) : K :=
  ∑ s, ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s g⁻¹)
end PI.Dv.GLatHermW


