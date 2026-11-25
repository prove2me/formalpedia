-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:37.896466+00:00
-- url     : https://prove2.me/theorems/5b72d21c-2fd7-4c14-87fd-9f4a8b79710b
-- title:
--   Exists Grouped Of Sublist
-- statement:
--   Definitions and structural lemmas for Exists Grouped Of Sublist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.ExpCong
section Abstract
variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)
def along (w : List ι) (f : A) : A := w.foldl (fun g a => D a g) f
def grouped (L : List ι) (m : ι → ℕ) : List ι := L.flatMap fun l => List.replicate (m l) l
end Abstract
variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
end GlobalTheory.ExpCong
namespace GlobalTheory
end GlobalTheory


