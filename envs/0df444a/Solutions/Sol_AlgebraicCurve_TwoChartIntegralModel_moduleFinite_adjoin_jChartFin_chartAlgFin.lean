-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.moduleFinite_adjoin_jChartFin_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1f3b8275-8900-57fc-97cc-fb2b963c6efa

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_moduleFinite_adjoin_jChartFin_chartAlgFin

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel Polynomial

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (hj : Transcendental K₀ j)
    [FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] :
    Module.Finite ↥(Algebra.adjoin R ({jChartFin R F j} : Set ↥(chartAlgFin R F j))) ↥(chartAlgFin R F j) := by
  classical

  let A : Subalgebra R F := Algebra.adjoin R ({j} : Set F)
  let C : Subalgebra R F := chartAlgFin R F j
  let Kj : IntermediateField K₀ F := IntermediateField.adjoin K₀ ({j} : Set F)
  have hAC : A ≤ C := adjoin_le_chartAlg R F {j}

  have hRK : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  have hRF : algebraMap R F = (algebraMap K₀ F).comp (algebraMap R K₀) := IsScalarTower.algebraMap_eq R K₀ F
  have haeval_map : ∀ p : R[X], aeval j (p.map (algebraMap R K₀)) = aeval j p := by
    intro p
    rw [aeval_def, aeval_def, eval₂_map, ← hRF]
  have hinj : Function.Injective (aeval (R := R) j) := by
    intro p q hpq
    apply Polynomial.map_injective (algebraMap R K₀) hRK
    apply (transcendental_iff_injective.mp hj)
    rw [haeval_map, haeval_map, hpq]
  let e : R[X] ≃ₐ[R] A :=
    (AlgEquiv.ofInjective (aeval j) hinj).trans (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval R j).symm)
  have he : ∀ p : R[X], ((e p : A) : F) = aeval j p := fun _ => rfl
  haveI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R[X] e.toRingEquiv
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv

  have hAK : ∀ x : F, x ∈ A → x ∈ Kj := by
    intro x hx
    have : A ≤ (Kj.toSubalgebra).restrictScalars R :=
      Algebra.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self K₀ j))
    exact this hx
  let toK : A →+* Kj :=
    { toFun := fun a => ⟨(a : F), hAK a a.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  letI algAK : Algebra A Kj := toK.toAlgebra
  have htoK : ∀ a : A, ((algebraMap A Kj a : Kj) : F) = (a : F) := fun _ => rfl
  haveI : IsScalarTower A Kj F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : FaithfulSMul A Kj :=
    (faithfulSMul_iff_algebraMap_injective A Kj).mpr (fun a b h => Subtype.ext (congrArg (fun z : Kj => (z : F)) h))
  haveI : IsFractionRing A Kj := by
    apply IsFractionRing.of_field
    intro z
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff K₀ (z : F)).mp z.2
    obtain ⟨br, hbr, hr⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) r
    obtain ⟨bs, hbs, hs⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) s
    set r' := IsLocalization.integerNormalization (nonZeroDivisors R) r with hr'
    set s' := IsLocalization.integerNormalization (nonZeroDivisors R) s with hs'

    have key : ∀ (p : K₀[X]) (p' : R[X]) (b : R), p'.map (algebraMap R K₀) = b • p →
        aeval j p' = algebraMap R F b * aeval j p := by
      intro p p' b h
      rw [← haeval_map p', h, ← algebraMap_smul K₀ b p, Polynomial.smul_eq_C_mul, map_mul, aeval_C, hRF, RingHom.comp_apply]
    have hr1 := key r r' br hr
    have hs1 := key s s' bs hs
    have hbr0 : algebraMap R F br ≠ 0 := fun h0 =>
      (nonZeroDivisors.ne_zero hbr) (by rw [hRF, RingHom.comp_apply, map_eq_zero] at h0; exact hRK (by rw [h0, map_zero]))
    have hbs0 : algebraMap R F bs ≠ 0 := fun h0 =>
      (nonZeroDivisors.ne_zero hbs) (by rw [hRF, RingHom.comp_apply, map_eq_zero] at h0; exact hRK (by rw [h0, map_zero]))
    refine ⟨e (Polynomial.C bs * r'), e (Polynomial.C br * s'), Subtype.ext ?_⟩
    show (z : F) = ((algebraMap A Kj (e (Polynomial.C bs * r')) : Kj) : F) / ((algebraMap A Kj (e (Polynomial.C br * s')) : Kj) : F)
    rw [htoK, htoK, he, he, map_mul, map_mul, aeval_C, aeval_C, hr1, hs1, hz]
    rw [show algebraMap R F bs * (algebraMap R F br * aeval j r) = (algebraMap R F br * algebraMap R F bs) * aeval j r by ring,
      show algebraMap R F br * (algebraMap R F bs * aeval j s) = (algebraMap R F br * algebraMap R F bs) * aeval j s by ring,
      mul_div_mul_left _ _ (mul_ne_zero hbr0 hbs0)]

  letI algAC : Algebra A C := (Subalgebra.inclusion hAC).toRingHom.toAlgebra
  haveI : IsScalarTower A C F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : IsIntegralClosure C A F :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, (mem_chartAlg_iff R F).mpr hx⟩, rfl⟩,
        fun ⟨y, hy⟩ => hy ▸ (mem_chartAlg_iff R F).mp y.2⟩ }

  haveI hfinA : Module.Finite A C := IsIntegralClosure.finite A Kj F C

  let B : Subalgebra R C := Algebra.adjoin R ({jChartFin R F j} : Set C)
  let jB : B := ⟨jChartFin R F j, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let φ : A →ₐ[R] B := (aeval jB).comp e.symm.toAlgHom
  have hφ : ∀ a : A, ((φ a : B) : C) = algebraMap A C a := by
    intro a
    obtain ⟨p, rfl⟩ := e.surjective a
    apply Subtype.ext
    show (((aeval jB (e.symm (e p)) : B) : C) : F) = ((e p : A) : F)
    rw [AlgEquiv.symm_apply_apply, he]
    calc (((aeval jB p : B) : C) : F) = C.val (B.val (aeval jB p)) := rfl
      _ = C.val (aeval (B.val jB) p) := by rw [(aeval_algHom_apply B.val jB p)]
      _ = aeval (C.val (B.val jB)) p := (aeval_algHom_apply C.val (B.val jB) p).symm
      _ = aeval j p := rfl
  letI : SMul A B := ⟨fun a b => φ a * b⟩
  haveI : IsScalarTower A B C := ⟨fun a b x => by
    show ((φ a * b : B) : C) * x = algebraMap A C a * ((b : C) * x)
    rw [Subalgebra.coe_mul, hφ, mul_assoc]⟩
  exact Module.Finite.of_restrictScalars_finite A B C

end S_AlgebraicCurve_TwoChartIntegralModel_moduleFinite_adjoin_jChartFin_chartAlgFin
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_moduleFinite_adjoin_jChartFin_chartAlgFin (solution)
