-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFormEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFormEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:52.845256+00:00
-- url     : https://prove2.me/theorems/91f63826-3aee-4b4a-aeb0-faee71e925bb
-- title:
--   Exists Form Eq One
-- statement:
--   Definitions and structural lemmas for Exists Form Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFormEqOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
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
namespace GlobalTheory.SimAlg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
theorem modN_zero (n : ℕ) : D.ModN n 0 := ⟨0, by simp⟩
theorem modN_add {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [smul_add]⟩
theorem modN_map {n : ℕ} {x : D.La} (f : D.La →ₗ[𝓞 E] D.La) (hx : D.ModN n x) : D.ModN n (f x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨f a, by rw [map_nsmul]⟩
def one (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := by simpa using modN_zero n
  inv n _ := ⟨LinearMap.id, fun a => by simpa using modN_zero n⟩
  mult n _ a b := by simp
def mul (g g' : Sim D) : Sim D where
  f n := g.f n ∘ₗ g'.f n
  ν n := g.ν n * g'.ν n
  tower n m hn hm a := by
    have h1 := g.tower n m hn hm (g'.f (n * m) a)
    have h2 := modN_map (g.f n) (g'.tower n m hn hm a)
    convert modN_add h1 h2 using 1
    simp
  inv n hn := by
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨h', hh'⟩ := g'.inv n hn
    refine ⟨h' ∘ₗ h, fun a => ⟨?_, ?_⟩⟩
    · convert modN_add (modN_map h' (hh (g'.f n a)).1) (hh' a).1 using 1
      simp
    · convert modN_add (modN_map (g.f n) (hh' (h a)).2) (hh a).2 using 1
      simp
  mult n hn a b := by
    have h1 := g.mult n hn (g'.f n a) (g'.f n b)
    have h2 := Dvd.dvd.mul_left (g'.mult n hn a b) (g.ν n)
    obtain ⟨c, hc⟩ := dvd_add h1 h2
    exact ⟨c, by simp only [LinearMap.comp_apply]; linear_combination hc⟩
end GlobalTheory.SimAlg


