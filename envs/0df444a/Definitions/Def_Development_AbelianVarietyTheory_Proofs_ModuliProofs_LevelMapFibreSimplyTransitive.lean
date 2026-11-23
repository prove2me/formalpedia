-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:47.803993+00:00
-- url     : https://prove2.me/theorems/63f5bdef-37a8-4986-8d3a-a7f3aa663103
-- title:
--   Level Map Fibre Simply Transitive
-- statement:
--   Definitions and structural lemmas for Level Map Fibre Simply Transitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

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
noncomputable section
namespace GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
section Algebra
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
def tateTransport {Q' : Type} [Group Q'] {act' : 𝓞 E → Q' → Q'} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIso D k Q act e) (φ : Q ≃* Q') (hact : ∀ c x, φ (act c x) = act' c (φ x))
    (he : ∀ n x y c, e n x y c → e' n (φ x) (φ y) c) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := φ (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, hact]
  ker n hn a := by rw [map_eq_one_iff φ φ.injective, I.ker n hn]
  onto n hn x := by
    obtain ⟨x, rfl⟩ := φ.surjective x
    rw [← map_pow, map_eq_one_iff φ φ.injective, I.onto n hn]
    exact exists_congr fun a => φ.injective.eq_iff.symm
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := he _ _ _ _ (I.isom n hn a b)
end Algebra
section Points
variable {S S' T : Scheme.{0}}
end Points
section Main
variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}
end Main
end GlobalTheory.LevelFibre


