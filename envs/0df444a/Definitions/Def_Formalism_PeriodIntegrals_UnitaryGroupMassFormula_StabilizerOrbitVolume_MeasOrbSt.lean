-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasOrbSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasOrbSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:26.350917+00:00
-- url     : https://prove2.me/theorems/62482086-e683-4ae3-b14c-ba52f75deace
-- title:
--   Meas Orb St
-- statement:
--   Definitions and structural lemmas for Meas Orb St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/MeasOrbSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
def MeasOrb : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ, IsAdm F E Φ →
    Measurable fun g : HA (AF F) σ J => Φ (g • ratTup (AF F) X0)
def MeasGrp : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  MeasurableMul (HA (AF F) σ J) ∧ MeasurableInv (HA (AF F) σ J)
end PI.VolStabSW


