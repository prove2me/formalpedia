-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f7d1d0ff-7336-51de-9dae-0cd3387f8634

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv

set_option autoImplicit false

open AlgebraicCurve

universe u

namespace E137

theorem mem_chartAlg_of_ringEquiv
    {R : Type u} [CommRing R] {F F' : Type u} [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (e : F ≃+* F') (he : ∀ r : R, e (algebraMap R F r) = algebraMap R F' r) (S : Set F) (x : F)
    (hx : x ∈ TwoChartIntegralModel.chartAlg R F S) : e x ∈ TwoChartIntegralModel.chartAlg R F' (e '' S) := by
  let eₐ : F ≃ₐ[R] F' := AlgEquiv.ofRingEquiv (f := e) he
  have hmap : (Algebra.adjoin R S).map eₐ.toAlgHom = Algebra.adjoin R (e '' S) := AlgHom.map_adjoin eₐ.toAlgHom S
  let φ : ↥(Algebra.adjoin R S) →+* ↥(Algebra.adjoin R (e '' S)) :=
    { toFun := fun b => ⟨e b, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨b, b.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hφ : (algebraMap ↥(Algebra.adjoin R (e '' S)) F').comp φ = e.toRingHom.comp (algebraMap ↥(Algebra.adjoin R S) F) :=
    RingHom.ext fun b => rfl
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at hx ⊢
  obtain ⟨p, hm, hp⟩ := hx
  refine ⟨p.map φ, hm.map φ, ?_⟩
  rw [Polynomial.eval₂_map, hφ]
  change Polynomial.eval₂ (e.toRingHom.comp _) (e.toRingHom x) p = 0
  rw [← Polynomial.hom_eval₂, hp, map_zero]

end E137

theorem solution
    {R : Type u} [CommRing R] {F F' : Type u} [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (e : F ≃+* F') (he : ∀ r : R, e (algebraMap R F r) = algebraMap R F' r) :
    (∀ (S : Set F) (x : F),
      x ∈ TwoChartIntegralModel.chartAlg R F S ↔ e x ∈ TwoChartIntegralModel.chartAlg R F' (e '' S)) ∧
    ∀ (j : F) [Fact (j ≠ 0)] [Fact (e j ≠ 0)],
      (∃ ε : ↥(TwoChartIntegralModel.chartAlgInf R F j) ≃+* ↥(TwoChartIntegralModel.chartAlgInf R F' (e j)),
        (∀ b, ((ε b : ↥(TwoChartIntegralModel.chartAlgInf R F' (e j))) : F') = e (b : F)) ∧
        ∀ r : R, ε (algebraMap R _ r) = algebraMap R _ r) ∧
      (∃ ε : ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃+* ↥(TwoChartIntegralModel.chartAlgFin R F' (e j)),
        (∀ b, ((ε b : ↥(TwoChartIntegralModel.chartAlgFin R F' (e j))) : F') = e (b : F)) ∧
        ∀ r : R, ε (algebraMap R _ r) = algebraMap R _ r) := by
  have he' : ∀ r : R, e.symm (algebraMap R F' r) = algebraMap R F r := fun r => by
    rw [← he, RingEquiv.symm_apply_apply]
  have key : ∀ (S : Set F) (x : F),
      x ∈ TwoChartIntegralModel.chartAlg R F S ↔ e x ∈ TwoChartIntegralModel.chartAlg R F' (e '' S) := by
    intro S x
    refine ⟨E137.mem_chartAlg_of_ringEquiv e he S x, fun h => ?_⟩
    have := E137.mem_chartAlg_of_ringEquiv e.symm he' (e '' S) (e x) h
    simpa [Set.image_image] using this
  let eₐ : F ≃ₐ[R] F' := AlgEquiv.ofRingEquiv (f := e) he

  have hmapS : ∀ S : Set F, (TwoChartIntegralModel.chartAlg R F S).map eₐ.toAlgHom =
      TwoChartIntegralModel.chartAlg R F' (e '' S) := by
    intro S
    ext y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
      exact (key S x).mp hx
    · intro hy
      refine Subalgebra.mem_map.mpr ⟨e.symm y, ?_, by simp [eₐ]⟩
      rw [key, RingEquiv.apply_symm_apply]; exact hy
  have mk : ∀ (S : Set F) (S' : Set F') (hS : e '' S = S'),
      ∃ ε : ↥(TwoChartIntegralModel.chartAlg R F S) ≃+* ↥(TwoChartIntegralModel.chartAlg R F' S'),
        (∀ b, ((ε b : ↥(TwoChartIntegralModel.chartAlg R F' S')) : F') = e (b : F)) ∧
        ∀ r : R, ε (algebraMap R _ r) = algebraMap R _ r := by
    intro S S' hS
    let ε : ↥(TwoChartIntegralModel.chartAlg R F S) ≃ₐ[R] ↥(TwoChartIntegralModel.chartAlg R F' S') :=
      (eₐ.subalgebraMap (TwoChartIntegralModel.chartAlg R F S)).trans
        (Subalgebra.equivOfEq _ _ ((hmapS S).trans (by rw [hS])))
    refine ⟨ε.toRingEquiv, fun b => rfl, fun r => ?_⟩
    exact ε.commutes r
  refine ⟨key, fun j _ _ => ⟨?_, ?_⟩⟩
  · exact mk {j⁻¹} {(e j)⁻¹} (by rw [Set.image_singleton, map_inv₀])
  · exact mk {j} {e j} (by rw [Set.image_singleton])

end S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv (solution)
