-- Prove2me | Definitions.Def_Eden_FactorLimits
-- name    : Eden_FactorLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:17:34.92487+00:00
-- url     : https://prove2.me/theorems/0244d44e-68df-4a3f-8c64-14f00b24c56a
-- title:
--   Factor Limits
-- statement:
--   Definitions and structural lemmas for Factor Limits, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorLimits.lean

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
namespace Eden
def limitingSquaredRadius (s : ℝ) : ℝ :=
  if s < 1 then 0 else if s = 1 then 1 else 2
def factorExponents (c : ℝ) (p : PhaseSpace) : Fin 5 → ℝ :=
  ![radialRate (limitingSquaredRadius (radiusSq₁ p)),
    tangentialRate (limitingSquaredRadius (radiusSq₁ p)),
    radialRate (limitingSquaredRadius (radiusSq₂ p)),
    tangentialRate (limitingSquaredRadius (radiusSq₂ p)), -c]
end Eden


