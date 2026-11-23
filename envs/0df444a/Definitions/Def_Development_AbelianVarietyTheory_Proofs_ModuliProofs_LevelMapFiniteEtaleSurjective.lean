-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:43.198012+00:00
-- url     : https://prove2.me/theorems/13f33aed-2ba6-46f4-91c7-b131101bba8f
-- title:
--   Level Map Finite Etale Surjective
-- statement:
--   Definitions and structural lemmas for Level Map Finite Etale Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
noncomputable def baseOf (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) : Base l F where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := (IntermediateField.inclusion h).toRingHom (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := (IntermediateField.inclusion h).toRingHom (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (RingHom.injective _)
def ObjCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)
variable {D : Datum H} {l l₂ : Level H}
def Represents {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B} (o : Obj D l b s) : Prop :=
  ∀ (S : Scheme.{0}) (s' : S ⟶ Sp B) (o' : Obj D l b s'), IsReduced S →
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o' o f)
end GlobalTheory.LevelCover


