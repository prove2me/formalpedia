-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:49.488811+00:00
-- url     : https://prove2.me/theorems/afd13b33-0e0a-40d1-8a3d-82bd8f01c01a
-- title:
--   Is Algebraic New
-- statement:
--   Definitions and structural lemmas for Is Algebraic New, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
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
open MvPolynomial
noncomputable section
namespace AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)
abbrev plusMap : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Option ι) P.FunField := D.extMap
def oldMap : MvPolynomial (Coord n) ℤ →+* MvPolynomial (Option ι) P.FunField :=
  (plusMap D).comp (D.liftOld : MvPolynomial (Coord n) ℤ →+* MvPolynomial (Coord D.extSizes) ℤ)
end AddBlockDimension
end
end GroundTheory.Heights₂.Heights


