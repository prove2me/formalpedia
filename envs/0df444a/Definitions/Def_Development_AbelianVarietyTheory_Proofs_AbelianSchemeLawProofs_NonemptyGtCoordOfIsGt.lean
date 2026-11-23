-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:25:22.39252+00:00
-- url     : https://prove2.me/theorems/1c7bd555-f884-4e38-8e2d-bc7b386134fa
-- title:
--   Nonempty Gt Coord Of Is Gt
-- statement:
--   Definitions and structural lemmas for Nonempty Gt Coord Of Is Gt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
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
namespace GlobalTheory.WeightGen
abbrev GermFn (Y : Scheme.{0}) := ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), (Z.presheaf.stalk z)ˣ
section
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
def HasGen (N : LB B) (c : GermFn P) : Prop :=
  ∃ s : ∀ j, Γ(G, q ⁻¹ᵁ N.U j)ˣ,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι), q (r z) ∈ N.U j → q (r z) ∈ N.U j' →
      gm r z _ (s j') = gm (r ≫ q) z _ (N.g j j') * gm r z _ (s j)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι), q (p (r z)) ∈ N.U j →
      gm (r ≫ a) z _ (s j) = c Z r z * gm (r ≫ p) z _ (s j)
variable {q a p}
end
section Datum
variable {S : Scheme.{0}}
noncomputable def wt (X : Type) [AddCommGroup X] (G : Over S) (χ : X) :
    GermFn (splitTorus S X ⊗ G).left :=
  fun _ r z => gm (r ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ)
variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)
noncomputable abbrev act : splitTorus S E.X ⊗ G ⟶ G :=
  lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ[G]
attribute [local instance] SplitExt.free SplitExt.finite
end Datum
section Coord
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
end Coord
end GlobalTheory.WeightGen
namespace GlobalTheory
open WeightGen
end GlobalTheory


