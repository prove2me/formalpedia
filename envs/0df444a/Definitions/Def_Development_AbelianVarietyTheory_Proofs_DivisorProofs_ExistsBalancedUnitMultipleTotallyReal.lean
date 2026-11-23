-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBalancedUnitMultipleTotallyReal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBalancedUnitMultipleTotallyReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:13.31136+00:00
-- url     : https://prove2.me/theorems/d7b76d4f-7689-4bed-8cdb-a0927c7629fe
-- title:
--   Exists Balanced Unit Multiple Totally Real
-- statement:
--   Definitions and structural lemmas for Exists Balanced Unit Multiple Totally Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBalancedUnitMultipleTotallyReal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
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
noncomputable section
namespace GlobalTheory.BalancedUnits
open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem
end GlobalTheory.BalancedUnits


