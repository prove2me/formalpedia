-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:34.399624+00:00
-- url     : https://prove2.me/theorems/f598dfef-0cc8-45d7-9ef6-6092cec75264
-- title:
--   Haar Transv
-- statement:
--   Definitions and structural lemmas for Haar Transv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean

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
open ValuativeRel Module Matrix
namespace PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def tγ (t : Matrix.TransvectionStruct ι K) : ι → ValueGroupWithZero K :=
  Function.update 1 t.i (max (valuation K t.c) 1)
end PI.ProdFormulaE.HaarBox
end


