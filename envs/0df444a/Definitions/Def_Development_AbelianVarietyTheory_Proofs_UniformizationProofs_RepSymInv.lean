-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:45.152856+00:00
-- url     : https://prove2.me/theorems/c0167e90-9c8c-471e-b0f4-b97bd9ee4e5c
-- title:
--   Rep Sym Inv
-- statement:
--   Definitions and structural lemmas for Rep Sym Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RepSymInv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
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
namespace GlobalTheory.UU.BoxSec
section Rep
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
def Rep (P : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ X) → L.ι), T.left.presheaf.stalk z) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)),
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = P U h) ∧
    ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → sval s r.left z J = v T r z J
variable {L Y}
end Rep
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}
def cubP {U : Type} [CommGroup U] (h : (Y.left ⟶ D.P.A.left) → U) (x x' y : Y ⟶ D.P.A) : U :=
  h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : Y ⟶ D.P.A).left)⁻¹
end GlobalTheory.UU.BoxSec


