-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:30.70489+00:00
-- url     : https://prove2.me/theorems/1a3506bf-eba3-4bdc-bfdc-f709b4159c97
-- title:
--   Integrable Fd
-- statement:
--   Definitions and structural lemmas for Integrable Fd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace FlatWeightedEstimates
def cD (n : ℕ) (p : Fin (n * 2)) : ℂ := ![1 / 2, -Complex.I / 2] (finProdFinEquiv.symm p).2
def vD (n : ℕ) (p : Fin (n * 2)) : V n :=
  ![bas n (finProdFinEquiv.symm p).1, Complex.I • bas n (finProdFinEquiv.symm p).1]
    (finProdFinEquiv.symm p).2
def cS : Fin 4 → ℂ := ![1 / 2, Complex.I / 2, -1 / 2, -Complex.I / 2]
def vS (n : ℕ) (j k : Fin n) : Fin 4 → V n :=
  ![bas n j, Complex.I • bas n j, bas n k, Complex.I • bas n k]
end FlatWeightedEstimates
end
end ReciprocityTheory.L2DbarEstimates.F


