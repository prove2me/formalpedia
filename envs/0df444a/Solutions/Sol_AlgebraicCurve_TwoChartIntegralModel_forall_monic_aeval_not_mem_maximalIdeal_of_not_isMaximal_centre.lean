-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ae24dbbd-12b0-5b58-914a-7e1e81e70c6e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre

set_option autoImplicit false

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

set_option maxHeartbeats 0

open Polynomial

theorem solution
    (R F : Type) [CommRing R] [IsLocalRing R] [Field F] [Algebra R F] (j : F)
    (V : ValuationSubring F)
    (hVR : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a : R, a ∈ maximalIdeal R → (⟨algebraMap R F a, hVR a⟩ : ↥V) ∈ maximalIdeal ↥V)
    (hVC : ∀ c : ↥(chartAlgFin R F j), (c : F) ∈ V)
    (y : Ideal ↥(chartAlgFin R F j))
    (hy : ∀ c : ↥(chartAlgFin R F j), c ∈ y ↔ ∀ hc : (c : F) ∈ V, (⟨(c : F), hc⟩ : ↥V) ∈ maximalIdeal ↥V)
    (hny : ¬ y.IsMaximal) :
    ∀ hjV : j ∈ V, ∀ p : Polynomial R, p.Monic → ∀ hp : Polynomial.aeval j (p.map (algebraMap R F)) ∈ V,
      (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V := by
  classical
  intro hjV p hpm hp hpmem

  let toV : ↥(chartAlgFin R F j) →+* ↥V :=
    { toFun := fun c => ⟨(c : F), hVC c⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hyeq : y = (maximalIdeal ↥V).comap toV := by
    ext c; rw [Ideal.mem_comap]; exact (hy c).trans ⟨fun h => h (hVC c), fun h _ => h⟩
  haveI hyprime : y.IsPrime := by rw [hyeq]; exact Ideal.comap_isPrime _ _

  let jC : ↥(chartAlgFin R F j) := jChartFin R F j
  have hjC : (jC : F) = j := rfl
  let Cval : ↥(chartAlgFin R F j) →+* F := (chartAlgFin R F j).val.toRingHom
  have hCval : ∀ c, Cval c = (c : F) := fun _ => rfl
  have hCvalR : Cval.comp (algebraMap R ↥(chartAlgFin R F j)) = algebraMap R F := RingHom.ext (fun _ => rfl)
  have hpjC : ((Polynomial.aeval jC p : ↥(chartAlgFin R F j)) : F) = Polynomial.aeval j (p.map (algebraMap R F)) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self, RingHom.id_comp,
      ← hCval, Polynomial.hom_eval₂, hCvalR, hCval, hjC]
  have hpy : Polynomial.aeval jC p ∈ y := by
    rw [hy]; intro hc
    have : (⟨((Polynomial.aeval jC p : ↥(chartAlgFin R F j)) : F), hc⟩ : ↥V) = ⟨_, hp⟩ := Subtype.ext hpjC
    rw [this]; exact hpmem

  have hmy : ∀ a : R, a ∈ maximalIdeal R → algebraMap R ↥(chartAlgFin R F j) a ∈ y := by
    intro a ha
    rw [hy]; intro hc
    have : (⟨((algebraMap R ↥(chartAlgFin R F j) a : ↥(chartAlgFin R F j)) : F), hc⟩ : ↥V) = ⟨algebraMap R F a, hVR a⟩ :=
      Subtype.ext rfl
    rw [this]; exact hVm a ha

  haveI : IsDomain (↥(chartAlgFin R F j) ⧸ y) := Ideal.Quotient.isDomain y
  let πₐ : ↥(chartAlgFin R F j) →ₐ[R] (↥(chartAlgFin R F j) ⧸ y) := Ideal.Quotient.mkₐ R y
  let π : ↥(chartAlgFin R F j) →+* (↥(chartAlgFin R F j) ⧸ y) := Ideal.Quotient.mk y
  have hππ : ∀ c, πₐ c = π c := fun _ => rfl
  have hπp : Polynomial.aeval (πₐ jC) p = 0 := by
    rw [Polynomial.aeval_algHom_apply πₐ jC p, hππ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpy
  have hπp' : p.eval₂ (algebraMap R (↥(chartAlgFin R F j) ⧸ y)) (πₐ jC) = 0 := by
    rw [← Polynomial.aeval_def]; exact hπp
  let S := AdjoinRoot p
  haveI : Module.Finite R S := Module.Finite.of_basis (AdjoinRoot.powerBasis' hpm).basis
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let φ : S →+* (↥(chartAlgFin R F j) ⧸ y) := AdjoinRoot.lift (algebraMap R _) (πₐ jC) hπp'
  have hφmk : ∀ g : Polynomial R, φ (AdjoinRoot.mk p g) = g.eval₂ (algebraMap R _) (πₐ jC) := fun g => AdjoinRoot.lift_mk _ g
  have hφR : ∀ r : R, φ (algebraMap R S r) = algebraMap R _ r := by
    intro r
    have : algebraMap R S r = AdjoinRoot.mk p (Polynomial.C r) := (AdjoinRoot.algebraMap_eq p ▸ rfl)
    rw [this, hφmk, Polynomial.eval₂_C]
  letI algS : Algebra S (↥(chartAlgFin R F j) ⧸ y) := φ.toAlgebra
  haveI : IsScalarTower R S (↥(chartAlgFin R F j) ⧸ y) := IsScalarTower.of_algebraMap_eq (fun r => (hφR r).symm)

  have hint : Algebra.IsIntegral S (↥(chartAlgFin R F j) ⧸ y) := by
    refine ⟨fun d => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hc : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (c : F) := c.2
    let fr : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({j} : Set F)) :=
      (Polynomial.aeval j : Polynomial R →ₐ[R] F).codRestrict (Algebra.adjoin R ({j} : Set F))
        (fun g => Polynomial.aeval_mem_adjoin_singleton R j)
    have hfrsurj : Function.Surjective fr := by
      intro r
      have : (r : F) ∈ (Polynomial.aeval j : Polynomial R →ₐ[R] F).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
      obtain ⟨g, hg⟩ := this
      exact ⟨g, Subtype.ext hg⟩
    obtain ⟨Q, hQm, hQ⟩ := hc
    obtain ⟨Qg, hQg, -, hQgm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts Q).mpr (fun n => hfrsurj (Q.coeff n))) hQm
    let f : Polynomial R →+* F := (Polynomial.aeval j : Polynomial R →ₐ[R] F).toRingHom
    have hrelF : Qg.eval₂ f (c : F) = 0 := by
      have h1 : Polynomial.aeval (c : F) Q = 0 := hQ
      rw [← hQg, Polynomial.aeval_def, Polynomial.eval₂_map] at h1
      convert h1 using 2
      rfl
    let fC : Polynomial R →+* ↥(chartAlgFin R F j) := (Polynomial.aeval jC : Polynomial R →ₐ[R] ↥(chartAlgFin R F j)).toRingHom
    have hfC : Cval.comp fC = f := by
      apply Polynomial.ringHom_ext
      · intro r
        change Cval (Polynomial.aeval jC (Polynomial.C r : Polynomial R)) = Polynomial.aeval j (Polynomial.C r : Polynomial R)
        rw [Polynomial.aeval_C, Polynomial.aeval_C]; rfl
      · change Cval (Polynomial.aeval jC (Polynomial.X : Polynomial R)) = Polynomial.aeval j (Polynomial.X : Polynomial R)
        rw [Polynomial.aeval_X, Polynomial.aeval_X]; rfl
    have hrelC : Qg.eval₂ fC c = 0 := by
      apply Subtype.ext
      rw [← hCval, Polynomial.hom_eval₂, hfC, hCval]
      exact hrelF
    let fD : Polynomial R →+* (↥(chartAlgFin R F j) ⧸ y) := π.comp fC
    have hrelD : Qg.eval₂ fD (π c) = 0 := by
      change Qg.eval₂ (π.comp fC) (π c) = 0
      rw [← Polynomial.hom_eval₂, hrelC, map_zero]
    letI alg1 : Algebra (Polynomial R) (↥(chartAlgFin R F j) ⧸ y) := fD.toAlgebra
    have hI1 : @IsIntegral (Polynomial R) (↥(chartAlgFin R F j) ⧸ y) _ _ alg1 (π c) :=
      ⟨Qg, hQgm, by rw [Polynomial.eval₂_eq_eval_map] at hrelD ⊢; exact hrelD⟩
    letI alg2 : Algebra (Polynomial R) S := (AdjoinRoot.mk p).toAlgebra
    haveI tow : IsScalarTower (Polynomial R) S (↥(chartAlgFin R F j) ⧸ y) := by
      refine IsScalarTower.of_algebraMap_eq (fun g => ?_)
      change fD g = φ (AdjoinRoot.mk p g)
      rw [hφmk]
      change π (Polynomial.aeval jC g) = Polynomial.eval₂ (algebraMap R _) (πₐ jC) g
      rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply πₐ jC g, hππ]
    exact hI1.tower_top

  let P : Ideal S := RingHom.ker φ
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime φ
  have hPcomap : P.comap (algebraMap R S) = maximalIdeal R := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _))
    · intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hφR]
      change π (algebraMap R ↥(chartAlgFin R F j) a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmy a ha)
  have hPmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (by rw [hPcomap]; exact IsLocalRing.maximalIdeal.isMaximal R)

  have hbot : (⊥ : Ideal (↥(chartAlgFin R F j) ⧸ y)).IsMaximal := by
    haveI := hint
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := S) (⊥ : Ideal (↥(chartAlgFin R F j) ⧸ y)) ?_
    have : (⊥ : Ideal (↥(chartAlgFin R F j) ⧸ y)).comap (algebraMap S (↥(chartAlgFin R F j) ⧸ y)) = P := by
      ext s; rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]; rfl
    rw [this]; exact hPmax

  apply hny
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  have hF : IsField ((↥(chartAlgFin R F j) ⧸ y) ⧸ (⊥ : Ideal (↥(chartAlgFin R F j) ⧸ y))) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).mp hbot
  exact MulEquiv.isField hF (RingEquiv.quotientBot (↥(chartAlgFin R F j) ⧸ y)).symm.toMulEquiv

end S_AlgebraicCurve_TwoChartIntegralModel_forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre (solution)
