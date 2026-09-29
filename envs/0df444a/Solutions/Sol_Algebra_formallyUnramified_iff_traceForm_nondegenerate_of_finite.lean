-- Prove2me | solution 1 for Algebra.formallyUnramified_iff_traceForm_nondegenerate_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5c4abd8a-7e99-573d-9947-733dcfe78bb3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite

set_option autoImplicit false

universe u

namespace TraceFormCrit

theorem nondeg_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (Algebra.traceForm R S).Nondegenerate ↔
      ∀ x : S, (∀ y, Algebra.trace R S (x * y) = 0) → x = 0 := by
  constructor
  · intro h x hx
    exact h.1 x (fun y => by rw [Algebra.traceForm_apply]; exact hx y)
  · intro h
    refine ⟨fun x hx => h x fun y => ?_, fun y hy => h y fun x => ?_⟩
    · have := hx y
      rwa [Algebra.traceForm_apply] at this
    · have := hy x
      rwa [Algebra.traceForm_apply, mul_comm] at this

theorem nondeg_of_algEquiv {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) (h : (Algebra.traceForm R C).Nondegenerate) :
    (Algebra.traceForm R B).Nondegenerate := by
  rw [nondeg_iff] at h ⊢
  intro x hx
  have hex : e x = 0 := h (e x) fun z => by
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [← map_mul, Algebra.trace_eq_of_algEquiv]
    exact hx y
  exact (map_eq_zero_iff e e.injective).mp hex

theorem nondeg_iff_of_algEquiv {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) :
    (Algebra.traceForm R B).Nondegenerate ↔ (Algebra.traceForm R C).Nondegenerate :=
  ⟨nondeg_of_algEquiv e.symm, nondeg_of_algEquiv e⟩

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

theorem nondeg_pi_iff {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Module.Finite K (A i)] :
    (Algebra.traceForm K (∀ i, A i)).Nondegenerate ↔
      ∀ i, (Algebra.traceForm K (A i)).Nondegenerate := by
  simp only [nondeg_iff]
  constructor
  · intro h i x hx
    have key := h (Pi.single i x) fun y => by
      rw [trace_pi_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        rw [Pi.mul_apply, Pi.single_eq_same]
        exact hx (y j)
      · rw [Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul, map_zero]
    have := congrFun key i
    rwa [Pi.single_eq_same] at this
  · intro h x hx
    funext i
    refine h i (x i) fun y => ?_
    have key := hx (Pi.single i y)
    rw [trace_pi_apply, Finset.sum_eq_single i] at key
    · rwa [Pi.mul_apply, Pi.single_eq_same] at key
    · intro j _ hj
      rw [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero, map_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem nondeg_iff_isSeparable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    (Algebra.traceForm K L).Nondegenerate ↔ Algebra.IsSeparable K L := by
  constructor
  · intro h
    by_contra hs
    have h0 := Algebra.trace_eq_zero_of_not_isSeparable hs
    rw [nondeg_iff] at h
    exact one_ne_zero (h 1 fun y => by rw [h0, LinearMap.zero_apply])
  · intro _
    exact traceForm_nondegenerate K L

theorem main_of_isReduced (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] :
    Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : ∀ I : MaximalSpectrum B, Field (B ⧸ I.asIdeal) := fun I => Ideal.Quotient.field I.asIdeal
  haveI : ∀ I : MaximalSpectrum B, Module.Finite K (B ⧸ I.asIdeal) := fun I =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let e : B ≃ₐ[K] ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal :=
    (IsArtinianRing.equivPi B).restrictScalars K
  have h1 : Algebra.FormallyUnramified K B ↔
      Algebra.FormallyUnramified K (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal) :=
    ⟨fun _ => Algebra.FormallyUnramified.of_equiv e,
     fun _ => Algebra.FormallyUnramified.of_equiv e.symm⟩
  rw [h1, Algebra.FormallyUnramified.pi_iff, nondeg_iff_of_algEquiv e, nondeg_pi_iff]
  refine forall_congr' fun I => ?_
  rw [Algebra.FormallyUnramified.iff_isSeparable K (B ⧸ I.asIdeal), nondeg_iff_isSeparable]

theorem isReduced_of_nondeg (K B : Type*) [Field K] [CommRing B] [Algebra K B]
    (h : (Algebra.traceForm K B).Nondegenerate) : IsReduced B := by
  refine ⟨fun x hx => (nondeg_iff.mp h) x fun y => ?_⟩
  exact (Algebra.isNilpotent_trace_of_isNilpotent
    (Commute.isNilpotent_mul_right (Commute.all x y) hx)).eq_zero

end TraceFormCrit

open TraceFormCrit in
theorem solution
    (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B] :
    Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by
  constructor
  · intro h
    haveI : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field K B
    exact (main_of_isReduced K B).mp h
  · intro h
    haveI : IsReduced B := isReduced_of_nondeg K B h
    exact (main_of_isReduced K B).mpr h

end S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite
end P2MW
export P2MW.S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite (solution)
