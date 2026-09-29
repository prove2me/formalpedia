-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/434897c3-035a-5468-a42a-45545f41eb63

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial

namespace W10XK3Eb

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem residue_comp_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) :
    (R.residue : R.integers →+* Fbar).comp (eval₂RingHom (constHom R) f) =
      (eval₂RingHom (algebraMap (ResidueField A) Fbar) (R.residue f)).comp
        (Polynomial.mapRingHom (IsLocalRing.residue A)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coe_mapRingHom, map_C]
    exact residue_constHom R a
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coe_mapRingHom,
      Polynomial.map_X]

theorem subtype_comp_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) :
    (R.integers.subtype : R.integers →+* F).comp (eval₂RingHom (constHom R) f) =
      eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
    exact coe_constHom R a
  · simp

end W10XK3Eb
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero.W10XK3Eb"

open W10XK3Eb

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (f u : R.integers)
    (hu : ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (u : F) = 0) :
    IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue f}) (R.residue u) := by
  classical
  set k := IsLocalRing.ResidueField A
  obtain ⟨p, hmon, heq⟩ := hu
  let Φ : Polynomial A →+* R.integers := eval₂RingHom (constHom R) f
  have heqO : p.eval₂ Φ u = 0 := by
    have h := Polynomial.hom_eval₂ p Φ R.integers.subtype u
    rw [subtype_comp_eval₂_constHom] at h
    exact Subtype.ext (h.trans heq)
  let ψ : Polynomial k →+* Fbar := eval₂RingHom (algebraMap k Fbar) (R.residue f)
  have heqbar :
      (p.map (Polynomial.mapRingHom (IsLocalRing.residue A))).eval₂ ψ (R.residue u) = 0 := by
    have h2 := Polynomial.hom_eval₂ p Φ R.residue u
    rw [residue_comp_eval₂_constHom] at h2
    rw [Polynomial.eval₂_map, ← h2, heqO, map_zero]
  set S : Subalgebra k Fbar := Algebra.adjoin k {R.residue f}
  have hfS : R.residue f ∈ S := Algebra.self_mem_adjoin_singleton k (R.residue f)
  let η : Polynomial k →+* S := eval₂RingHom (algebraMap k S) ⟨R.residue f, hfS⟩
  have hψη : (algebraMap S Fbar).comp η = ψ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [η, ψ]
    · simp [η, ψ]
  refine ⟨(p.map (Polynomial.mapRingHom (IsLocalRing.residue A))).map η,
    (hmon.map _).map η, ?_⟩
  rw [Polynomial.eval₂_map, hψη]
  exact heqbar

end
end S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero (solution)
