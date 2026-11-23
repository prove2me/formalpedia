-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:45.963718+00:00
-- url     : https://prove2.me/theorems/c51d0dc5-4d31-4e28-8f54-c1371f878f88
-- title:
--   Exists Modular Function
-- statement:
--   Definitions and structural lemmas for Exists Modular Function, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ExistsModularFunction.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula
open PI ModW ModW.MG
open Classical in

def modFun {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (hG : IsMatGroup G)
    (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  if h : g ∈ G then (Measure.modularCharacterFun (mk hG g h) : ℝ) else 1
end PI.QuotSetU.UnitaryGroupMassFormula


