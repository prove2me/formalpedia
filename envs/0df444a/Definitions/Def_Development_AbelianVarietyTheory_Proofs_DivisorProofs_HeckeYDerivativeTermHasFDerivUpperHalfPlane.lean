-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlane
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:34.048784+00:00
-- url     : https://prove2.me/theorems/5a64f845-a33f-4fa0-b62b-ac1854e9881e
-- title:
--   Hecke YDerivative Term Has FDeriv Upper Half Plane
-- statement:
--   Definitions and structural lemmas for Hecke YDerivative Term Has FDeriv Upper Half Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeYDerivativeTermHasFDerivUpperHalfPlane.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical
noncomputable section
namespace GlobalTheory.HeckeTwo
end GlobalTheory.HeckeTwo


