-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:55.460508+00:00
-- url     : https://prove2.me/theorems/32e4d85e-072c-46e4-9f99-17f5c5ee8e5c
-- title:
--   PProj Arith Var
-- statement:
--   Definitions and structural lemmas for PProj Arith Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
namespace ProjectiveArithmeticVariety
variable (K : Type) [Field K] [NumberField K] (n : ℕ)
abbrev xc (j : Fin (n + 1)) : ProjField K (n + 1) :=
  algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j)
def aff (l : Fin n) : ProjField K (n + 1) := xc K n l.succ / xc K n 0
def dehom : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K :=
  (aeval (Fin.cases 1 X : Fin (n + 1) → MvPolynomial (Fin n) K)).toRingHom
end ProjectiveArithmeticVariety
end
end GroundTheory.Heights₂.Heights


