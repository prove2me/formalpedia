-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:23.160353+00:00
-- url     : https://prove2.me/theorems/363b69a1-a211-4d3a-86c6-2410eb92aa61
-- title:
--   Univ Identity
-- statement:
--   Definitions and structural lemmas for Univ Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnivIdentity.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
namespace GlobalTheory.UT.SymFrame
section Rep
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
def GRep (P : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ X) → L.ι), (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (s : LB.Gen (LB.LinComb L φ ε)), s.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = P U h) ∧
    ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → val s r.left z J = v T r z J
variable {L Y}
end Rep
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
abbrev nuLB (D : DegPre R) (N : ℕ) : LB D.P.A.left := LB.LinComb D.P.L (K := Fin 4)
  ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
  ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
end GlobalTheory.UT.SymFrame
end


