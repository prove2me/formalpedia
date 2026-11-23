-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:00.074848+00:00
-- url     : https://prove2.me/theorems/6507bdd0-07fb-4b1a-8885-c5135beb3458
-- title:
--   Symmetric Frame Phi Pow Order Eq Id
-- statement:
--   Definitions and structural lemmas for Symmetric Frame Phi Pow Order Eq Id, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
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
namespace GlobalTheory.UT.PhiOrder
section Alg
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
def pot (θ : A → A → A → U) (b : A) (n : ℕ) : U := ∏ j ∈ Finset.range n, cubN θ j 1 b b
end Alg
section Formal
variable {A U : Type} [CommGroup A] [CommGroup U]
def wN (h : A → U) (x : A) (j : ℕ) : U :=
  h (x ^ (j + 1)) * (h (x ^ j))⁻¹ * (h (x ^ 2) ^ j)⁻¹ * h x ^ (2 * j) * (h x)⁻¹ * h 1 * (h 1 ^ j)⁻¹
end Formal
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
def Rep (V : ∀ (T : Over (Spec (CommRingCat.of R))) (_ : T ⟶ D.P.A) (z : T.left),
      ((T.left ⟶ D.P.A.left) → D.P.L.ι) → (T.left.presheaf.stalk z)ˣ)
    (W : ∀ (U : Type) [CommGroup U], ((D.P.A ⟶ D.P.A) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L φ ε)),
    t.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U),
      ∏ k, h (φ k) ^ ε k = W U (fun a => h a.left)) ∧
    ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val t x.left z J = V T x z J
variable {D}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
end GlobalTheory.UT.PhiOrder
end


