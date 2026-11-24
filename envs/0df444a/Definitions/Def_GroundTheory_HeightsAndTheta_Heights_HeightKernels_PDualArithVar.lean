-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:31.654724+00:00
-- url     : https://prove2.me/theorems/d0cbcf45-0c30-47b5-b6e1-42420c61b070
-- title:
--   PDual Arith Var
-- statement:
--   Definitions and structural lemmas for PDual Arith Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
namespace DualArithmeticVariety
variable {K : Type} [Field K]
def evalForm (m : ℕ) : (Fin m → K) →ₗ[K] ProjField K m :=
  Fintype.linearCombination K fun j => algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j)
variable [NumberField K] {i : ℕ}
variable {F : HermLattice K i} {T : Type}
end DualArithmeticVariety
end
end GroundTheory.Heights₂.Heights


