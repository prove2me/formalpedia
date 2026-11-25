-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:15.93095+00:00
-- url     : https://prove2.me/theorems/cfe8dfd9-87c3-5ddb-81b0-0877b879fbbb
-- title:
--   Locally Trivial Torus Quotient Flat Surjective Cosets
-- statement:
--   Definitions and structural lemmas for Locally Trivial Torus Quotient Flat Surjective Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocallyTrivialTorusQuotientFlatSurjectiveCosets.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.LocTriv
section Algebra
variable {R A X : Type} [CommRing R] [CommRing A] [AddCommGroup X]
end Algebra
variable {S : Scheme.{0}}
def incl (Z : Over S) (W : Z.left.Opens) : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
section Chart
variable [IsMonHom i] [IsAffineHom q.left] {V : B.left.Opens} (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a)
  (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤
    ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
  (u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ)
include hV h₀ hU
end Chart
end GlobalTheory.LocTriv
end


