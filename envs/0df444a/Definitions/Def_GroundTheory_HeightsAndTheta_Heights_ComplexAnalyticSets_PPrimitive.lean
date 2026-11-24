-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:11.081838+00:00
-- url     : https://prove2.me/theorems/cb038303-94be-4420-8cab-cfb530a396f5
-- title:
--   PPrimitive
-- statement:
--   Definitions and structural lemmas for PPrimitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitive.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
def funField (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] : Type :=
  FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)
instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] : Field (funField J) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))
instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (funField J) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))
instance (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) (funField J) :=
  inferInstanceAs (IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)))
end
end GroundTheory.Heights₂.Heights.ComplexSets


