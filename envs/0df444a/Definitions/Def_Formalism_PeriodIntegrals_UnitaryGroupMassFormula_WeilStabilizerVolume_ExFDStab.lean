-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStab
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:26.367853+00:00
-- url     : https://prove2.me/theorems/fea90553-45d3-4c2d-9736-44c898305a8d
-- title:
--   Ex FDStab
-- statement:
--   Definitions and structural lemmas for Ex FDStab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExFDStab.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
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
open scoped TensorProduct
def SCHA : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)
def DiscHF : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  DiscreteTopology (HFinIn (AF F) σ J)
end PI.VolStabW


