-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:57.483358+00:00
-- url     : https://prove2.me/theorems/e459f374-d134-4eb4-85ab-f6829796d3db
-- title:
--   Nilpotent Subgroup Representation
-- statement:
--   Definitions and structural lemmas for Nilpotent Subgroup Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
variable [CharZero K]
end CompanionTheory.D.gk.RF
namespace CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
end CompanionTheory.D.gk.RF


