-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:35:29.584823+00:00
-- url     : https://prove2.me/theorems/0ee279c3-edbe-4a84-88f1-1b24fb6e1e56
-- title:
--   Exists Series Of Natural On Nilpotent
-- statement:
--   Definitions and structural lemmas for Exists Series Of Natural On Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfNaturalOnNilpotent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
noncomputable abbrev serNatI (R₀ κ : Type) [CommRing R₀] (N : ℕ) : Ideal (MvPolynomial κ R₀) :=
  Ideal.span (Set.range fun j : κ => (MvPolynomial.X j : MvPolynomial κ R₀) ^ N)
end GlobalTheory


