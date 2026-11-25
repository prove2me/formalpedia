-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_EvalValChartCoord
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_EvalValChartCoord
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:16.110143+00:00
-- url     : https://prove2.me/theorems/6d4f8c82-9f6f-4f2d-aa5f-9fe2c509b32b
-- title:
--   Eval Val Chart Coord
-- statement:
--   Definitions and structural lemmas for Eval Val Chart Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/EvalValChartCoord.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemBasicOpenSecHomIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace AffPres
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)} (P : AffPres s)
end AffPres
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
end
end ReciprocityTheory.AnForm.R


