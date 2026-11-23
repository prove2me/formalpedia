-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:50.163832+00:00
-- url     : https://prove2.me/theorems/ef472a73-1430-4a06-bfb4-64014ab5bd57
-- title:
--   Is Locally Constant Test Representation Tensor Product
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Test Representation Tensor Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology
namespace GlobalTheory.JR.WeilProd.TensorTest
section Basic
variable {X : Type} [TopologicalSpace X]
end Basic
section Prod
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
end Prod
end GlobalTheory.JR.WeilProd.TensorTest
namespace GlobalTheory.JR.WeilProd
open TensorTest
end GlobalTheory.JR.WeilProd


