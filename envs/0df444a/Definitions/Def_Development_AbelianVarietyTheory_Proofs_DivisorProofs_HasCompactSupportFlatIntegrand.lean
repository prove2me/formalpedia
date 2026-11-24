-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:11.495903+00:00
-- url     : https://prove2.me/theorems/928a4167-eacc-4eca-97d4-0bfe4a2ff2a3
-- title:
--   Has Compact Support Flat Integrand
-- statement:
--   Definitions and structural lemmas for Has Compact Support Flat Integrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
end GlobalTheory.FunObj


