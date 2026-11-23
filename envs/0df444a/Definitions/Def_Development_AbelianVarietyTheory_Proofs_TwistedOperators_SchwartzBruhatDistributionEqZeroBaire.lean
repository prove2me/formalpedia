-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:43.566617+00:00
-- url     : https://prove2.me/theorems/9ab31a01-1181-43da-b962-eba7a85893d2
-- title:
--   Schwartz Bruhat Distribution Eq Zero Baire
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Distribution Eq Zero Baire, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatDistributionEqZeroBaire.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
namespace GlobalTheory.BaireDistribution
section General
variable {X : Type} [TopologicalSpace X]
end General
section Group
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end Group
end GlobalTheory.BaireDistribution


