-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:20.024879+00:00
-- url     : https://prove2.me/theorems/6a666a12-cddc-425e-843e-565001e66edb
-- title:
--   Fib Top
-- statement:
--   Definitions and structural lemmas for Fib Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibTop.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExOmTOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
def FreeOpen : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  IsOpen {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen {X : Fin a → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}
end PI.VolStabW


