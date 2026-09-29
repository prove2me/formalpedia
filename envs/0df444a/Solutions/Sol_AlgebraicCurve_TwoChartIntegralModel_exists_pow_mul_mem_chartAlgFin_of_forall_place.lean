-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_pow_mul_mem_chartAlgFin_of_forall_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7bd9b588-8dea-5e9b-b45a-6fe1cd2c2c37

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place

set_option autoImplicit false

open IsLocalRing Polynomial AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

namespace H3eKey

section

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

theorem isIntegral_of_adjoin_le {S₁ S₂ : Subalgebra R A} (h : S₁ ≤ S₂) {x : A}
    (hx : IsIntegral ↥S₁ x) : IsIntegral ↥S₂ x :=
  hx.map_of_comp_eq (Subalgebra.inclusion h).toRingHom (RingHom.id A) (by ext; rfl)

theorem isIntegral_of_le_of_forall_isIntegral {S₁ S₂ : Subalgebra R A} (h : S₁ ≤ S₂)
    (hint : ∀ y : A, y ∈ S₂ → IsIntegral ↥S₁ y) {x : A} (hx : IsIntegral ↥S₂ x) : IsIntegral ↥S₁ x := by
  letI alg : Algebra ↥S₁ ↥S₂ := (Subalgebra.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ↥S₁ ↥S₂ A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral ↥S₁ ↥S₂ := by
    refine ⟨fun y => ?_⟩
    have hy : IsIntegral ↥S₁ (y : A) := hint y y.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥S₁ ↥S₂ A) Subtype.val_injective).1 hy
  exact isIntegral_trans x hx

end

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
  (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
  (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (j : F)

theorem isIntegrallyClosedIn_chartAlg (S : Set F) : IsIntegrallyClosedIn ↥(chartAlg R F S).toSubring F := by
  refine (Subring.isIntegrallyClosedIn_iff).2 ?_
  intro x hx'

  have hx : IsIntegral ↥(chartAlg R F S) x := hx'
  have : IsIntegral ↥(Algebra.adjoin R S) x :=
    isIntegral_of_le_of_forall_isIntegral (adjoin_le_chartAlg R F S)
      (fun y hy => (mem_chartAlg_iff R F).1 hy) hx
  exact (mem_chartAlg_iff R F).2 this

include hϖ in

theorem exists_pow_mul_mem_chartAlgFin [Fact (j ≠ 0)]
    [FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    (x : F) (hx : ∀ v : AlgebraicCurve.Place K₀ F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    ∃ k : ℕ, algebraMap R F ϖ ^ k * x ∈ chartAlgFin R F j := by
  classical
  set w : F := algebraMap R F ϖ with hwdef
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2 hϖ
  have hinjRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hw0 : w ≠ 0 := by
    rw [hwdef]; exact (map_ne_zero_iff _ hinjRF).2 hirr.ne_zero

  let S : Set F := {w, j}
  let C' : Subalgebra R F := chartAlg R F (insert w⁻¹ S)
  haveI : IsIntegrallyClosedIn ↥C'.toSubring F := isIntegrallyClosedIn_chartAlg R F _

  have hxC' : x ∈ C' := by
    by_contra hxC
    obtain ⟨V, hCV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := C'.toSubring) hxC

    have hRV : ∀ r : R, algebraMap R F r ∈ V := fun r => hCV (C'.algebraMap_mem r)
    have hwinvV : w⁻¹ ∈ V := hCV (subset_chartAlg R F _ (Set.mem_insert _ _))
    have hjV : j ∈ V := hCV (subset_chartAlg R F _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton j))))

    have hK₀V : ∀ a : K₀, algebraMap K₀ F a ∈ V := by
      intro a
      obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv]
      refine V.mul_mem _ _ (hRV r) ?_
      have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
      obtain ⟨n, u, hsu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hirr
      rw [hsu, map_mul, map_pow, ← hwdef, mul_inv, ← inv_pow]
      refine V.mul_mem _ _ ?_ (pow_mem hwinvV n)
      have hu : algebraMap R F ((u⁻¹ : Rˣ) : R) = (algebraMap R F (u : R))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
      rw [← hu]; exact hRV _
    by_cases hVtop : V = ⊤
    · exact hxV (hVtop.symm ▸ ValuationSubring.mem_top x)
    obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional j V hK₀V hVtop
    exact hxV (hv ▸ hx v (hv.symm ▸ hjV))

  obtain ⟨k, hk⟩ := exists_pow_mul_mem_chartAlg (R := R) (F := F) (S := S) (s := w) (Set.mem_insert _ _) hw0 hxC'
  refine ⟨k, ?_⟩

  have hadj : Algebra.adjoin R S ≤ Algebra.adjoin R {j} := by
    refine Algebra.adjoin_le ?_
    rintro y (rfl | hy)
    · exact Subalgebra.algebraMap_mem _ ϖ
    · rw [Set.mem_singleton_iff.1 hy]; exact Algebra.self_mem_adjoin_singleton R j
  have hxk : IsIntegral ↥(Algebra.adjoin R S) (w ^ k * x) := (mem_chartAlg_iff R F).1 hk
  exact (mem_chartAlg_iff R F).2 (isIntegral_of_adjoin_le hadj hxk)

end H3eKey

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)]
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : F) (hx : ∀ v : Place K₀ F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    ∃ k : ℕ, algebraMap R F ϖ ^ k * x ∈ chartAlgFin R F j := by
  haveI := hFD
  exact H3eKey.exists_pow_mul_mem_chartAlgFin R ϖ hϖ K₀ F j x hx

end S_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place (solution)
