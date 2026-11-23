-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:52.768408+00:00
-- url     : https://prove2.me/theorems/67c45ec0-cae1-404b-a747-bcaa1ce9a553
-- title:
--   Exists Irreducible Of Fixed
-- statement:
--   Definitions and structural lemmas for Exists Irreducible Of Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean

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
namespace GlobalTheory.CompanionTheory.ProdSub
section Abstract
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
end Abstract
section Product
variable {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [AddCommGroup V] [Module ℂ V]
end Product
end GlobalTheory.CompanionTheory.ProdSub


