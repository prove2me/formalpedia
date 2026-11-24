-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:59.796916+00:00
-- url     : https://prove2.me/theorems/7ff5e0d7-08fc-46f3-8a87-fd69500a8cb1
-- title:
--   Statements Div Push Mult Complex
-- statement:
--   Definitions and structural lemmas for Statements Div Push Mult Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsDivPushMultComplex.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def DivPushMultComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I W : Ideal (MRing ι))
    (Wa : Ideal (MRingOver ℂ ι)),
    W ∈ I.minimalPrimes → IsHorizontal W →
    Wa ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    multAt I W = multAt (I.map (MvPolynomial.map (Int.castRingHom ℂ))) Wa
end GroundTheory.Heights₂.Heights.Targets


