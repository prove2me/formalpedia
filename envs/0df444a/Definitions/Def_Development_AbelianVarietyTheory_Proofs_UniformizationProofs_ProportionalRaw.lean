-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:01:41.291312+00:00
-- url     : https://prove2.me/theorems/c4339154-2e03-41ea-ada2-09ca0d7779f0
-- title:
--   Proportional Raw
-- statement:
--   Definitions and structural lemmas for Proportional Raw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.UU.SchurComp
section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
theorem gs_zero (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp
abbrev Vals (L : LB X) (Y : Scheme.{0}) : Type :=
  ∀ p : Σ z : Y, {J : (Y ⟶ X) → L.ι // Good L z J}, Y.presheaf.stalk p.1
def germs (L : LB X) (Y : Scheme.{0}) : Γ(Y, ⊤) →+* Vals L Y where
  toFun a p := gs (𝟙 Y) p.1 ⊤ a
  map_one' := funext fun p => by rw [gs_eq (𝟙 Y) p.1 ⊤ trivial, map_one, map_one]; rfl
  map_mul' a b := funext fun p => gs_mul (𝟙 Y) p.1 ⊤ trivial a b
  map_zero' := funext fun p => gs_zero _ _ _
  map_add' a b := funext fun p => gs_add (𝟙 Y) p.1 ⊤ trivial a b
end General
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
end GlobalTheory.UU.SchurComp
end


