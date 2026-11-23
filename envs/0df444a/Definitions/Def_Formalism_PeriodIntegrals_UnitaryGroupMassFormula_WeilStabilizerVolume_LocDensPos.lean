-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensPos
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:15.888877+00:00
-- url     : https://prove2.me/theorems/3e215f5d-79ba-468d-9b07-bb5a8cda5da6
-- title:
--   Loc Dens Pos
-- statement:
--   Definitions and structural lemmas for Loc Dens Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensPos.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal
namespace LocPosW
end LocPosW
open LocPosW
def LBInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a)),
    μinf.IsAddHaarMeasure → νinf.IsAddHaarMeasure →
    ∀ W : Set (Fin a → Fin M → Ainf F ⊗[F] E), IsOpen W → ratTup (F := F) (Ainf F) X0 ∈ W →
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT),
      ∀ S ⊆ N, MeasurableSet S →
        c * νinf S ≤ μinf ((gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W)
end PI.VolStabW


