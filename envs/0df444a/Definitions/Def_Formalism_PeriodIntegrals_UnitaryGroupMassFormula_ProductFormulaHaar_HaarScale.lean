-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarScale
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:40.39706+00:00
-- url     : https://prove2.me/theorems/f2bee960-0261-47c5-ba86-82e66b407758
-- title:
--   Haar Scale
-- statement:
--   Definitions and structural lemmas for Haar Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarScale.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
namespace PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]
end PI.ProdFormulaE.HaarBox


