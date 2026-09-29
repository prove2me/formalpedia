-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4e34fb72-5830-510e-b8ab-1ae52073b9a7

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers
import Theorems.Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
import Theorems.Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve IsLocalRing Polynomial

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (f : F) (m : ℕ)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∈ V → f ∈ V)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∉ V →
      f * ((x : F) ^ m)⁻¹ ∈ V)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      (∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m) ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) f = 0 := by
  classical

  have hxL : Transcendental L (x : F) :=
    RegularProlongation.transcendental_of_residue_transcendental A R x hx

  have hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) f := by
    set s : Set F := Set.range (algebraMap L F) ∪ {(x : F)} with hs
    have h := iInf_valuationSubring_superset (s := s)
    have hmem : f ∈ (integralClosure (Subring.closure s) F).toSubring := by
      rw [← h]
      simp only [Subring.mem_iInf]
      rintro ⟨V, hV⟩
      exact h₁ V (fun c => hV (Or.inl ⟨c, rfl⟩)) (hV (Or.inr rfl))
    have hint0 : IsIntegral (Subring.closure s) f := hmem
    have hcl : Subring.closure s = (Algebra.adjoin L ({(x : F)} : Set F)).toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm

    refine hint0.map_of_comp_eq (Subring.inclusion hcl.le) (RingHom.id F) ?_
    ext a
    exact (Subring.coe_inclusion hcl.le a).symm

  set LxA : Subalgebra L F := Algebra.adjoin L ({(x : F)} : Set F) with hLxA
  set q : Polynomial LxA := minpoly LxA f with hq
  have hqmon : q.Monic := minpoly.monic hint
  have hqf : Polynomial.aeval f q = 0 := minpoly.aeval LxA f
  set d := q.natDegree with hd

  have hrange : (Polynomial.aeval (R := L) (x : F)).range = LxA :=
    (Algebra.adjoin_singleton_eq_range_aeval L (x : F)).symm
  have hinj : Function.Injective (Polynomial.aeval (R := L) (x : F)) :=
    transcendental_iff_injective.mp hxL
  let e : Polynomial L ≃ₐ[L] LxA :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := L) (x : F)) hinj).trans
      (Subalgebra.equivOfEq _ _ hrange)
  have he : ∀ a : LxA, (Polynomial.aeval (x : F)) (e.symm a) = (a : F) := by
    intro a
    have happ := (AlgEquiv.ofInjective (Polynomial.aeval (R := L) (x : F)) hinj).apply_symm_apply
      ((Subalgebra.equivOfEq _ _ hrange).symm a)
    exact congrArg Subtype.val happ
  have he1 : e.symm 1 = 1 := map_one e.symm
  have he0 : e.symm 0 = 0 := map_zero e.symm

  have hx0 : (x : F) ≠ 0 := by
    intro h0
    apply hx
    have : x = (0 : R.integers) := Subtype.ext h0
    rw [this, map_zero]
    exact isAlgebraic_zero

  have hcA : ∀ j i, (e.symm (q.coeff j)).coeff i ∈ A := by
    intro j i
    refine AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers A R x hx
      (e.symm (q.coeff j)) ?_ i
    rw [he (q.coeff j)]
    exact AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
      A R x hx f hint h₃ j
  have hcdeg : ∀ j, (e.symm (q.coeff j)).natDegree ≤ (d - j) * m := by
    intro j
    exact Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
      (x : F) hxL hx0 f hint m h₂ j (e.symm (q.coeff j)) (he (q.coeff j))

  let lift : ℕ → Polynomial A := fun j =>
    (e.symm (q.coeff j)).support.sum fun i =>
      Polynomial.C ⟨(e.symm (q.coeff j)).coeff i, hcA j i⟩ * Polynomial.X ^ i
  have hlift : ∀ j, (lift j).map A.subtype = e.symm (q.coeff j) := by
    intro j
    ext i
    simp only [lift, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq _ i]
    by_cases hi : i ∈ (e.symm (q.coeff j)).support
    · simp [hi]
    · simp [hi, Polynomial.notMem_support_iff.mp hi]

  let p : Polynomial (Polynomial A) :=
    q.support.sum fun j => Polynomial.C (lift j) * Polynomial.X ^ j
  have hpcoeff : ∀ j, p.coeff j = if j ∈ q.support then lift j else 0 := by
    intro j
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq _ j _

  have hdsupp : d ∈ q.support := by
    rw [Polynomial.mem_support_iff, hd]
    exact hqmon.coeff_natDegree.symm ▸ one_ne_zero
  have hpd : p.coeff d = 1 := by
    rw [hpcoeff, if_pos hdsupp]
    have hqd : q.coeff d = 1 := hqmon.coeff_natDegree
    have : e.symm (q.coeff d) = 1 := by rw [hqd]; exact he1

    have hmap : (lift d).map A.subtype = 1 := by rw [hlift, this]
    have hAinj : Function.Injective (Polynomial.map (A.subtype : A →+* L)) :=
      Polynomial.map_injective _ Subtype.val_injective
    exact hAinj (by rw [hmap, Polynomial.map_one])
  have hpdeg : p.natDegree = d := by
    apply le_antisymm
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
      calc (Polynomial.C (lift j) * Polynomial.X ^ j).natDegree
          ≤ 0 + j := by
            refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
            simp [Polynomial.natDegree_X_pow]
        _ = j := zero_add j
        _ ≤ d := Polynomial.le_natDegree_of_mem_supp j hj
    · exact Polynomial.le_natDegree_of_ne_zero (hpd ▸ one_ne_zero)
  have hpmon : p.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hpdeg]; exact hpd
  refine ⟨p, hpmon, ?_, ?_⟩
  ·
    intro j
    rw [hpdeg, hpcoeff]
    split_ifs with hj
    ·
      have : (lift j).natDegree = (e.symm (q.coeff j)).natDegree := by
        rw [← hlift j]
        exact (Polynomial.natDegree_map_eq_of_injective Subtype.val_injective _).symm
      rw [this]; exact hcdeg j
    · simp
  ·

    have hinner : ∀ j, Polynomial.eval₂RingHom
        ((algebraMap L F).comp A.subtype) (x : F) (lift j) = (q.coeff j : F) := by
      intro j
      show Polynomial.eval₂ ((algebraMap L F).comp A.subtype) (x : F) (lift j) = (q.coeff j : F)
      rw [← Polynomial.eval₂_map, ← Polynomial.aeval_def, hlift j, he (q.coeff j)]
    calc p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) f
        = q.support.sum (fun j =>
            Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F) (lift j)
              * f ^ j) := by
          simp only [p, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
            Polynomial.eval₂_pow, Polynomial.eval₂_X]
      _ = q.support.sum (fun j => (q.coeff j : F) * f ^ j) := by
          exact Finset.sum_congr rfl (fun j _ => by rw [hinner j])
      _ = Polynomial.aeval f q := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range,
            ← Finset.sum_subset (Polynomial.supp_subset_range_natDegree_succ (p := q))]
          · rfl
          · intro j _ hj
            rw [Polynomial.notMem_support_iff.mp hj]
            simp
      _ = 0 := hqf

end S_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring (solution)
