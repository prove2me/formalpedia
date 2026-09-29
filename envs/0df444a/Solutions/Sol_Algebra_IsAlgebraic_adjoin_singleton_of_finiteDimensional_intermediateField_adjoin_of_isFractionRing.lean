-- Prove2me | solution 1 for Algebra.IsAlgebraic.adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d5a58802-f9ff-5982-9c67-f3a5981f27a6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing

set_option autoImplicit false

universe u

theorem solution
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
    (g : F) (hFD : FiniteDimensional ↥(IntermediateField.adjoin K ({g} : Set F)) F) :
    Algebra.IsAlgebraic ↥(Algebra.adjoin R ({g} : Set F)) F := by
  classical
  set S : Subalgebra R F := Algebra.adjoin R ({g} : Set F) with hS
  set E : IntermediateField K F := IntermediateField.adjoin K ({g} : Set F) with hE

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective R K)

  have hSE : ∀ s : F, s ∈ S → s ∈ E := by
    intro s hs
    have hle : S ≤ (E.toSubalgebra.restrictScalars R) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self K g))
    exact hle hs

  have hfrac : ∀ z : F, z ∈ E → ∃ a b : F, a ∈ S ∧ b ∈ S ∧ b ≠ 0 ∧ z * b = a := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      exact ⟨x, 1, Algebra.subset_adjoin hx, one_mem _, one_ne_zero, mul_one _⟩
    | algebraMap k =>
      obtain ⟨x, y, hy, hk⟩ := IsFractionRing.div_surjective (A := R) k
      have hy0 : algebraMap R F y ≠ 0 := fun h => nonZeroDivisors.ne_zero hy (hRF (by rw [h, map_zero]))
      refine ⟨algebraMap R F x, algebraMap R F y, Subalgebra.algebraMap_mem _ _, Subalgebra.algebraMap_mem _ _, hy0, ?_⟩
      rw [← hk, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        div_mul_cancel₀ _ hy0]
    | add x y hx hy ihx ihy =>
      obtain ⟨a₁, b₁, ha₁, hb₁, hb₁0, h₁⟩ := ihx
      obtain ⟨a₂, b₂, ha₂, hb₂, hb₂0, h₂⟩ := ihy
      refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, add_mem (mul_mem ha₁ hb₂) (mul_mem ha₂ hb₁), mul_mem hb₁ hb₂,
        mul_ne_zero hb₁0 hb₂0, ?_⟩
      rw [← h₁, ← h₂]; ring
    | inv x hx ihx =>
      obtain ⟨a, b, ha, hb, hb0, h⟩ := ihx
      by_cases ha0 : a = 0
      · have hx0 : x = 0 := by
          rcases mul_eq_zero.mp (h.trans ha0) with h' | h'
          · exact h'
          · exact absurd h' hb0
        refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
        rw [hx0, inv_zero, zero_mul]
      · have hx0 : x ≠ 0 := by
          intro hx0; apply ha0; rw [← h, hx0, zero_mul]
        refine ⟨b, a, hb, ha, ha0, ?_⟩
        rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    | mul x y hx hy ihx ihy =>
      obtain ⟨a₁, b₁, ha₁, hb₁, hb₁0, h₁⟩ := ihx
      obtain ⟨a₂, b₂, ha₂, hb₂, hb₂0, h₂⟩ := ihy
      refine ⟨a₁ * a₂, b₁ * b₂, mul_mem ha₁ ha₂, mul_mem hb₁ hb₂, mul_ne_zero hb₁0 hb₂0, ?_⟩
      rw [← h₁, ← h₂]; ring

  letI algSE : Algebra ↥S ↥E :=
    ((S.val : ↥S →ₐ[R] F).toRingHom.codRestrict E.toSubring (fun s => hSE s.1 s.2)).toAlgebra
  have halgSE : ∀ s : ↥S, ((algebraMap ↥S ↥E s : ↥E) : F) = (s : F) := fun _ => rfl
  haveI : IsScalarTower ↥S ↥E F := IsScalarTower.of_algebraMap_eq (fun s => rfl)
  haveI : IsFractionRing ↥S ↥E := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      apply isUnit_iff_ne_zero.mpr
      intro h0
      have : ((y : ↥S) : F) = 0 := by
        have := congrArg (fun e : ↥E => (e : F)) h0
        simpa [halgSE] using this
      exact nonZeroDivisors.ne_zero y.2 (Subtype.ext this)
    · intro z
      obtain ⟨a, b, ha, hb, hb0, h⟩ := hfrac (z : F) z.2
      have hb0' : (⟨b, hb⟩ : ↥S) ≠ 0 := fun h' => hb0 (congrArg Subtype.val h')
      refine ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, mem_nonZeroDivisors_of_ne_zero hb0'⟩), ?_⟩
      apply Subtype.ext
      show (z : F) * (((algebraMap ↥S ↥E) ⟨b, hb⟩ : ↥E) : F) = (((algebraMap ↥S ↥E) ⟨a, ha⟩ : ↥E) : F)
      rw [halgSE, halgSE]
      exact h
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : F) = (y : F) := by
        have := congrArg (fun e : ↥E => (e : F)) hxy
        simpa [halgSE] using this
      rw [Subtype.ext this]
  haveI : Algebra.IsAlgebraic ↥E F := Algebra.IsAlgebraic.of_finite ↥E F
  refine ⟨fun x => ?_⟩
  exact (IsFractionRing.isAlgebraic_iff ↥S ↥E F).mpr (Algebra.IsAlgebraic.isAlgebraic x)

end S_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing
end P2MW
export P2MW.S_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing (solution)
