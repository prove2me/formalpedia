-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMono
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:18:11.999966+00:00
-- url     : https://prove2.me/theorems/39925480-b812-44f9-b08a-51f9e23dd8e9
-- title:
--   Prime To Part Level Exists Unique Mono
-- statement:
--   Definitions and structural lemmas for Prime To Part Level Exists Unique Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimeToPartLevelExistsUniqueMono.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
namespace GlobalTheory.Models
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.Models.sup_mul_sup_eq_of_coprime {R : Type} [CommRing R] {I J N : Ideal R}
    (h : I ⊔ J = ⊤) (hN : I * J ≤ N) : (I ⊔ N) * (J ⊔ N) = N := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le hN (Ideal.mul_le_inf.trans inf_le_right))
      (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
  · calc N = N * (I ⊔ J) := by rw [h, Ideal.mul_top]
      _ = N * I ⊔ N * J := Ideal.mul_sup _ _ _
      _ ≤ (I ⊔ N) * (J ⊔ N) := sup_le
          (by rw [mul_comm]; exact Ideal.mul_mono le_sup_left le_sup_right)
          (Ideal.mul_mono le_sup_right le_sup_left)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def divisorLevel (l : Level H) (m : ℕ) (hm : m ∣ l.M) (h3 : 3 ≤ m) : Level H where
  M := m
  three_le := h3
  odd := l.odd.of_dvd_nat hm
  Mb := l.Mb ⊔ Ideal.span {(m : 𝓞 E)}
  fromK := by
    apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        rintro a ⟨ha, ha'⟩
        exact ⟨Ideal.mem_sup_left ha, ha'⟩
      · apply Ideal.span_mono
        rintro a rfl
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ m⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
    refine sup_mul_sup_eq_of_coprime l.coprime ?_
    rw [l.prod]
    exact Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast hm)
  coprime := by
    rw [eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left (Ideal.map_mono le_sup_left)
  A := 1
  A_pos := one_pos
end GlobalTheory.Models


