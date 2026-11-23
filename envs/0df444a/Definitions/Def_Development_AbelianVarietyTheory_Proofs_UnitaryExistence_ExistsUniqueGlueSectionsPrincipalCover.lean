-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:57.792649+00:00
-- url     : https://prove2.me/theorems/244ea597-a8f2-450e-bd4a-520d5b5fc907
-- title:
--   Exists Unique Glue Sections Principal Cover
-- statement:
--   Definitions and structural lemmas for Exists Unique Glue Sections Principal Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
namespace GlobalTheory.SecGlue
section Fn
variable {X Y Z : Scheme.{0}}
variable {J : Type} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
end Fn
section Sec
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}
def Rel (h : Y ⟶ X) {q : X ⟶ A} {q' : Y ⟶ A} (s : LB.Sec (LB.LinComb L (fun _ : K => q) ε))
    (t : LB.Sec (LB.LinComb L (fun _ : K => q') ε)) : Prop :=
  ∀ (j : K → L.ι) (hh : LB.wchart L (fun _ : K => q') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : K => q) j),
    (h.appLE _ _ hh).hom (s.f j) = t.f j
end Sec
section Fib
variable {B : Scheme.{0}} (G : Over B) {S T : Scheme.{0}}
def Can (f : T ⟶ S) (x : S ⟶ B) (x' : T ⟶ B) (pm : (Over.mk x' ⊗ G).left ⟶ (Over.mk x ⊗ G).left) : Prop :=
  pm ≫ (snd (Over.mk x) G).left = (snd (Over.mk x') G).left ∧
    pm ≫ (fst (Over.mk x) G).left = (fst (Over.mk x') G).left ≫ f
variable {G}
theorem Can.comp {U : Scheme.{0}} {f : T ⟶ S} {g : U ⟶ T} {x : S ⟶ B} {x' : T ⟶ B} {x'' : U ⟶ B} {pm pm'}
    (h : Can G f x x' pm) (h' : Can G g x' x'' pm') : Can G (g ≫ f) x x'' (pm' ≫ pm) :=
  ⟨by rw [Category.assoc, h.1, h'.1], by
    rw [Category.assoc, h.2, ← Category.assoc, h'.2]
    exact Category.assoc _ _ _⟩
end Fib
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
end GlobalTheory.SecGlue


