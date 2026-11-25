-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:25.401948+00:00
-- url     : https://prove2.me/theorems/e9c3c4ae-86df-5d14-9efb-a9538b01bde6
-- title:
--   Exists Unique Limit
-- statement:
--   Definitions and structural lemmas for Exists Unique Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueLimit.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv

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
noncomputable section
namespace GlobalTheory.SecLimit
section Algebra
universe u
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {W W' W'' : Type u} [CommRing W] [CommRing W']
  [CommRing W''] {m : ℕ}
def comb (c : R →+* W) (b : Fin m → W) (z : Fin m → R) : W := ∑ i, c (z i) * b i
def IsBas (c : R →+* W) (S : Set W) (b : Fin m → W) : Prop :=
  (∀ i, b i ∈ S) ∧ ∀ s ∈ S, ∃! z : Fin m → R, s = comb c b z
end Algebra
section Values
variable {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]
abbrev Vals (Y : Scheme.{0}) : Type 1 :=
  ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : {J // Good L z J}), Z.presheaf.stalk z
def pull (h : Y' ⟶ Y) : Vals L Y →+* Vals L Y' where
  toFun w Z r z J := w Z (r ≫ h) z J
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def fn (Y : Scheme.{0}) : Γ(Y, ⊤) →+* Vals L Y where
  toFun a Z r z _ := gs r z ⊤ a
  map_one' := by funext Z r z J; rw [gs_eq r z ⊤ trivial, map_one, map_one]; rfl
  map_mul' _ _ := by funext Z r z J; exact gs_mul r z ⊤ trivial _ _
  map_zero' := by funext Z r z J; rw [gs_eq r z ⊤ trivial, map_zero, map_zero]; rfl
  map_add' _ _ := by funext Z r z J; exact gs_add r z ⊤ trivial _ _
def cst {R : Type} [CommRing R] (f : Y ⟶ Spec (CommRingCat.of R)) : R →+* Vals L Y :=
  (fn L Y).comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
variable {L}
def ev {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Vals L Y := fun _ r z J => sval s r z J.1
def evU {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε)) : (Vals L Y)ˣ where
  val _ r z J := (val u r z J.1).val
  inv _ r z J := (val u r z J.1).inv
  val_inv := by funext Z r z J; exact (val u r z J.1).val_inv
  inv_val := by funext Z r z J; exact (val u r z J.1).inv_val
variable (L) in

def secVals (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Set (Vals L Y) := Set.range (ev (L := L) (φ := φ) (ε := ε))
variable {φ : K → (Y ⟶ X)} {ε : K → ℤ}
end Values
end GlobalTheory.SecLimit


