-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:34.315014+00:00
-- url     : https://prove2.me/theorems/84ad6a81-feb1-4b63-983b-8c6ec79770fa
-- title:
--   Sum Support Rename
-- statement:
--   Definitions and structural lemmas for Sum Support Rename, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumSupportRename.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant

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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
namespace GlobalTheory.NabCol
section Fold
variable {ι β : Type}
def fo (D : ι → β → β) (L : List ι) (m : ι →₀ ℕ) (x : β) : β := L.foldr (fun l g => (D l)^[m l] g) x
end Fold
variable {k : Type} [CommRing k] {d n : ℕ}
def inCol (b : Fin n) (f : PS k 1 d) : PS k n d := ev (n := n) ![pt k d b] f
theorem gp (b : Fin n) : ∀ j, GP ((![pt k d b] : Fin 1 → Pt k n d) j) := single_point_zero_constant (gp_pt b)
def inColHom (b : Fin n) : PS k 1 d →+* PS k n d := (substAlgHom (gt_hasSubst _ (gp (k := k) (d := d) b))).toRingHom
def colD (F : Fin d → PS k 2 d) (c : Fin n) (u : Fin d → k) (b : Fin n) : PS k 1 d → PS k 1 d :=
  if c = b then Dof F u else id
end GlobalTheory.NabCol
namespace GlobalTheory
end GlobalTheory


