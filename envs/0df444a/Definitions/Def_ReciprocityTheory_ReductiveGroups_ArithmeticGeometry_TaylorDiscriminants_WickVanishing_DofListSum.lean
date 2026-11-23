-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:04.726973+00:00
-- url     : https://prove2.me/theorems/2f1ea09f-2ff3-4b3f-8857-ba60b9f921c2
-- title:
--   Dof List Sum
-- statement:
--   Definitions and structural lemmas for Dof List Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
section Dof
variable (F : Fin d → PS k 2 d) (v : Fin d → k)
end Dof
section Words
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
def T (w : List ι) (A : PS k 1 d) : PS k 1 d := w.foldr (fun l g => Dof F (u l) g) A
def splits : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | l :: w => (splits w).map (fun p => (l :: p.1, p.2)) ++ (splits w).map (fun p => (p.1, l :: p.2))
end Words
end ReciprocityTheory.ChartRestriction.G.TB.G2


