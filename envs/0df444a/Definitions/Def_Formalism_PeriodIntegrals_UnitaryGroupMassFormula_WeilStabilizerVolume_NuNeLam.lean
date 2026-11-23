-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeLam
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeLam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:38.870951+00:00
-- url     : https://prove2.me/theorems/758cf048-02fa-448d-a99c-1102d2a6bb0c
-- title:
--   Nu Ne Lam
-- statement:
--   Definitions and structural lemmas for Nu Ne Lam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/NuNeLam.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeilQuotMeas
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise
def OrbProper : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K →
    IsCompact ((fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ⁻¹' K)
end PI.VolStabW


