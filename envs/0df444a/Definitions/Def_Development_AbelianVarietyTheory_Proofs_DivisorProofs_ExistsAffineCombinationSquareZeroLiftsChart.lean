-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:16.07047+00:00
-- url     : https://prove2.me/theorems/23b727ba-4558-4f15-8e7d-3db421d8907f
-- title:
--   Exists Affine Combination Square Zero Lifts Chart
-- statement:
--   Definitions and structural lemmas for Exists Affine Combination Square Zero Lifts Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecGlue.CombEx
end GlobalTheory.SecGlue.CombEx
namespace GlobalTheory.SecGlue.CombEx
theorem mul_eq_zero_of_sq {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {s t : S} (hs : q s = 0) (ht : q t = 0) : s * t = 0 := by
  have h : s * t ∈ RingHom.ker q ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (RingHom.mem_ker.2 hs) (RingHom.mem_ker.2 ht)
  rw [hsq] at h
  exact (Submodule.mem_bot S).1 h
def combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S) (hq : ∀ i, q.comp (ψ i) = q.comp φ) :
    A →+* S where
  toFun x := φ x + ∑ i, a i * (ψ i x - φ x)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_mul' x y := by
    have hd : ∀ i z, q (ψ i z - φ z) = 0 := fun i z => by
      rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
    have hD : ∀ z, q (∑ i, a i * (ψ i z - φ z)) = 0 := fun z => by
      simp only [map_sum, map_mul, hd, mul_zero, Finset.sum_const_zero]
    have e1 : ∀ i, ψ i (x * y) - φ (x * y) = φ x * (ψ i y - φ y) + (ψ i x - φ x) * φ y := fun i => by
      have := mul_eq_zero_of_sq q hsq (hd i x) (hd i y)
      rw [map_mul, map_mul]; linear_combination this
    have e2 := mul_eq_zero_of_sq q hsq (hD x) (hD y)
    have s : ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
        φ x * ∑ i, a i * (ψ i y - φ y) + φ y * ∑ i, a i * (ψ i x - φ x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i]; ring
    show φ (x * y) + ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
      (φ x + ∑ i, a i * (ψ i x - φ x)) * (φ y + ∑ i, a i * (ψ i y - φ y))
    linear_combination s + map_mul φ x y - e2
end GlobalTheory.SecGlue.CombEx


