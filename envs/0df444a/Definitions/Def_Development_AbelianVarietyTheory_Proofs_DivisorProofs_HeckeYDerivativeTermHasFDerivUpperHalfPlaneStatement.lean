-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:57.929019+00:00
-- url     : https://prove2.me/theorems/4356cae6-5906-45af-9622-c61895019d6f
-- title:
--   Hecke YDerivative Term Has FDeriv Upper Half Plane Statement
-- statement:
--   Definitions and structural lemmas for Hecke YDerivative Term Has FDeriv Upper Half Plane Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlane
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


