-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:06.73681+00:00
-- url     : https://prove2.me/theorems/e2168653-9e0a-424a-8d76-00bb6c92f6a5
-- title:
--   Exists Section Of Transversal
-- statement:
--   Definitions and structural lemmas for Exists Section Of Transversal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.HenselZero
section Fibre
variable {O : Type} [CommRing O] [IsLocalRing O] {X Y : Scheme.{0}} {p : X ⟶ Sp O} {q : Y ⟶ Sp (ResidueField O)}
  {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
include hφ
end Fibre
end GlobalTheory.HenselZero
end


