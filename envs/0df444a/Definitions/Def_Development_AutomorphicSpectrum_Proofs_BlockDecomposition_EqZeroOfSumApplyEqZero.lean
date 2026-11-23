-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfSumApplyEqZero
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfSumApplyEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:51.812131+00:00
-- url     : https://prove2.me/theorems/bde2f7c6-3209-49ea-b98c-884252a446af
-- title:
--   Eq Zero Of Sum Apply Eq Zero
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Sum Apply Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfSumApplyEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
namespace GlobalTheory.CompanionTheory.EvalTensor
variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
end GlobalTheory.CompanionTheory.EvalTensor


