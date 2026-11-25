-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFgFib
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFgFib
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:35:10.823473+00:00
-- url     : https://prove2.me/theorems/d4da37ac-ecc5-54d5-9e4d-f37728f639fa
-- title:
--   PFg Fib
-- statement:
--   Definitions and structural lemmas for PFg Fib, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFgFib.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.QuantumDeterminants.BesselUnitaryEquiv
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm.Gram
def UnipotentHaarConjInvariant : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∀ μ0 : Measure (Mt k r),
    B.IsHaarOn (C2.N0set k r z) μ0 → ∀ c ∈ UWset k r z, μ0.map (conjM c) = μ0
end PI.UnitaryGroupMassFormula.DLm.Gram


