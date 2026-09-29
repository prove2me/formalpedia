-- Prove2me | solution 1 for Algebra.isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6a2a1e2b-15f1-5846-8b87-61cdbf13f509

import Mathlib
import Theorems.Thm_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field

set_option autoImplicit false

universe u

namespace L2bAux

theorem trace_pi_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (x : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b) x, Matrix.trace]
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply,
    Pi.mul_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i) (x i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [Pi.single_eq_same]

theorem isUnit_mk_pow_of_notMem {T : Type*} [CommRing T] {Q : Ideal T} (hQ : Q.IsMaximal) (n : ℕ)
    {x : T} (hx : x ∉ Q) : IsUnit (Ideal.Quotient.mk (Q ^ n) x) := by
  obtain ⟨y, i, hi, h⟩ := hQ.exists_inv hx
  have hnil : IsNilpotent (Ideal.Quotient.mk (Q ^ n) i) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi n⟩
  have h1 : Ideal.Quotient.mk (Q ^ n) y * Ideal.Quotient.mk (Q ^ n) x =
      1 - Ideal.Quotient.mk (Q ^ n) i := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Q ^ n)), ← map_sub]
    congr 1
    rw [← h]
    ring
  exact isUnit_of_mul_isUnit_right (h1 ▸ hnil.isUnit_one_sub)

theorem single_one_mul {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, MulZeroOneClass (A i)]
    (j : ι) (f : ∀ i, A i) : Pi.single j 1 * f = Pi.single j (f j) := by
  ext i
  rw [Pi.mul_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

theorem mul_single {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, MulZeroClass (A i)]
    (j : ι) (f : ∀ i, A i) (z : A j) : f * Pi.single j z = Pi.single j (f j * z) := by
  ext i
  rw [Pi.mul_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]

theorem traceForm_surjective_iff {κ R : Type*} [Field κ] [CommRing R] [Algebra κ R]
    [Module.Finite κ R] :
    Function.Surjective (Algebra.traceForm κ R) ↔ (Algebra.traceForm κ R).Nondegenerate := by
  have hdim : Module.finrank κ R = Module.finrank κ (Module.Dual κ R) := Subspace.dual_finrank_eq.symm
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim]
  constructor
  · intro h
    have hl : (Algebra.traceForm κ R).SeparatingLeft := by
      rw [LinearMap.separatingLeft_iff_ker_eq_bot]
      exact LinearMap.ker_eq_bot.mpr h
    refine ⟨hl, fun y hy => hl y fun x => ?_⟩
    rw [Algebra.traceForm_apply, mul_comm, ← Algebra.traceForm_apply]
    exact hy x
  · intro h
    have := h.1
    rw [LinearMap.separatingLeft_iff_ker_eq_bot] at this
    exact LinearMap.ker_eq_bot.mp this

end L2bAux

open L2bAux in
theorem solution
    (κ : Type u) [Field κ] (T : Type u) [CommRing T] [Algebra κ T] [Module.Finite κ T]
    (Q : Ideal T) [Q.IsPrime] :
    Algebra.IsUnramifiedAt κ Q ↔
      ∃ s ∉ Q, ∀ φ : Module.Dual κ T, ∃ x : T, ∀ y : T, φ (s * y) = Algebra.trace κ T (x * y) := by
  classical
  haveI : IsArtinianRing T := IsArtinianRing.of_finite κ T
  have hQ : Q.IsMaximal := IsArtinianRing.isMaximal_of_isPrime Q
  haveI : Fintype (MaximalSpectrum T) := Fintype.ofFinite _

  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := T)
  set N := n + 1 with hNdef
  have hN : nilradical T ^ N = 0 := by rw [hNdef, pow_succ, hn, zero_mul]
  have hbot : (⊥ : Ideal T) = nilradical T ^ N := by rw [hN]; rfl
  let R : MaximalSpectrum T → Type _ := fun I => T ⧸ I.asIdeal ^ N
  let eT : T ≃ₐ[T] (∀ I, R I) :=
    (AlgEquiv.quotientBot T T).symm.trans
      ((Ideal.quotientEquivAlgOfEq T hbot).trans (IsArtinianRing.quotNilradicalPowEquivPi T N))
  have heT : ∀ (x : T) (I : MaximalSpectrum T), eT x I = Ideal.Quotient.mk (I.asIdeal ^ N) x :=
    fun x I => rfl
  let eK : T ≃ₐ[κ] (∀ I, R I) := eT.restrictScalars κ
  have heK : ∀ x, eK x = eT x := fun x => rfl
  let j : MaximalSpectrum T := ⟨Q, hQ⟩
  haveI : ∀ I : MaximalSpectrum T, Module.Finite κ (R I) := fun I =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ (I.asIdeal ^ N)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective κ _)

  let e : T := eT.symm (Pi.single j 1)
  have heTe : eT e = Pi.single j 1 := eT.apply_symm_apply _
  have he_notMem : e ∉ Q := by
    intro he
    have h1 : Ideal.Quotient.mk (Q ^ N) e = 1 := by
      rw [← heT e j, heTe, Pi.single_eq_same]
    rw [← map_one (Ideal.Quotient.mk (Q ^ N)), Ideal.Quotient.eq] at h1
    have : (1 : T) ∈ Q := by
      have h2 : e - 1 ∈ Q := Ideal.pow_le_self (Nat.succ_ne_zero n) h1
      simpa using Q.sub_mem he h2
    exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr this)

  have htrace : ∀ x y : T, Algebra.trace κ T (x * y) =
      ∑ I, Algebra.trace κ (R I) (eT x I * eT y I) := fun x y => by
    rw [← Algebra.trace_eq_of_algEquiv eK, heK, map_mul, trace_pi_apply]
    rfl

  haveI : IsLocalization.AtPrime (R j) Q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      exact isUnit_mk_pow_of_notMem hQ N hs
    · intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      refine ⟨⟨x, 1⟩, ?_⟩
      change Ideal.Quotient.mk _ x * algebraMap T (R j) 1 = algebraMap T (R j) x
      rw [map_one, mul_one]
      rfl
    · intro x y hxy
      refine ⟨⟨e, he_notMem⟩, ?_⟩
      apply eT.injective
      change eT (e * x) = eT (e * y)
      rw [map_mul, map_mul, heTe, single_one_mul, single_one_mul, heT, heT]
      exact congrArg _ hxy
  have hstep2 : Algebra.IsUnramifiedAt κ Q ↔ Algebra.FormallyUnramified κ (R j) :=
    Algebra.FormallyUnramified.iff_of_equiv
      ((IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (R j)).restrictScalars κ)

  rw [hstep2, Algebra.formallyUnramified_iff_traceForm_nondegenerate_of_finite, ← traceForm_surjective_iff]

  constructor
  · intro hsurj
    refine ⟨e, he_notMem, fun φ => ?_⟩
    let φj : Module.Dual κ (R j) :=
      φ ∘ₗ eK.symm.toLinearMap ∘ₗ LinearMap.single κ R j
    obtain ⟨xj, hxj⟩ := hsurj φj
    refine ⟨eT.symm (Pi.single j xj), fun y => ?_⟩
    have hey : e * y = eT.symm (Pi.single j (eT y j)) := by
      apply eT.injective
      rw [map_mul, heTe, single_one_mul, eT.apply_symm_apply]
    rw [hey, htrace, Finset.sum_eq_single j, eT.apply_symm_apply, Pi.single_eq_same]
    · have := LinearMap.congr_fun hxj (eT y j)
      rw [Algebra.traceForm_apply] at this
      rw [this]
      rfl
    · intro I _ hI
      rw [eT.apply_symm_apply, Pi.single_eq_of_ne hI, zero_mul, map_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rintro ⟨s, hs, H⟩ ψ
    have hu : IsUnit (eT s j) := isUnit_mk_pow_of_notMem hQ N hs
    let φ : Module.Dual κ T :=
      ψ ∘ₗ (LinearMap.mulLeft κ (↑hu.unit⁻¹ : R j)) ∘ₗ (LinearMap.proj j) ∘ₗ eK.toLinearMap
    have hφ : ∀ t : T, φ t = ψ (↑hu.unit⁻¹ * eT t j) := fun t => rfl
    obtain ⟨x, hx⟩ := H φ
    refine ⟨eT x j, LinearMap.ext fun z => ?_⟩
    have key := hx (eT.symm (Pi.single j z))
    rw [htrace, Finset.sum_eq_single j, eT.apply_symm_apply, Pi.single_eq_same] at key
    · rw [Algebra.traceForm_apply, ← key, hφ]
      rw [map_mul eT, eT.apply_symm_apply, mul_single, Pi.single_eq_same, ← mul_assoc,
        IsUnit.val_inv_mul, one_mul]
    · intro I _ hI
      rw [eT.apply_symm_apply, Pi.single_eq_of_ne hI, mul_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

end S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field
end P2MW
export P2MW.S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field (solution)
