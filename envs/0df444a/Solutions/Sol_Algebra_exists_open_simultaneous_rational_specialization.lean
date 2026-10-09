-- Prove2me | solution 1 for Algebra.exists_open_simultaneous_rational_specialization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T17:29:41.983259+00:00
-- url     : https://prove2.me/submissions/4d081b9b-77ec-411e-b7dc-f81b3eb9ad26

import Theorems.Thm_PiTensorProduct_isOpenMap_comap_of_quasiFinite
import Mathlib

section

set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators TensorProduct
noncomputable section

namespace PiTensorProduct

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
  {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]

/-- The universal algebra map induced by a finite family of algebra maps. -/
def familyLift {B : Type*} [CommRing B] [Algebra A B]
    (e : ∀ i, R i →ₐ[A] B) : (⨂[A] i, R i) →ₐ[A] B :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra A ι B).compLinearMap
    (fun i => (e i).toLinearMap))
    (by simp)
    (by intro x y; simp [Finset.prod_mul_distrib])

@[simp] theorem familyLift_tprod {B : Type*} [CommRing B] [Algebra A B]
    (e : ∀ i, R i →ₐ[A] B) (x : ∀ i, R i) :
    familyLift e (tprod A x) = ∏ i, e i (x i) := by
  simp [familyLift, liftAlgHom, lift.tprod]

@[simp] theorem familyLift_single {B : Type*} [CommRing B] [Algebra A B]
    (e : ∀ i, R i →ₐ[A] B) (i : ι) (x : R i) :
    familyLift e (singleAlgHom i x) = e i x := by
  rw [singleAlgHom_apply, familyLift_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hji]
  · simp

theorem tprod_eq_prod_single (x : ∀ i, R i) :
    tprod A x = ∏ i, singleAlgHom i (x i) := by
  simp only [singleAlgHom_apply, ← tprod_prod]
  congr 1
  ext j
  simp

/-- Finitely many finitely generated algebras have a finitely generated tensor product. -/
theorem finiteType_family [∀ i, Algebra.FiniteType A (R i)] :
    Algebra.FiniteType A (⨂[A] i, R i) := by
  classical
  choose s hs using fun i => (Algebra.FiniteType.out (R := A) (A := R i))
  let T : Set (⨂[A] i, R i) := ⋃ i, singleAlgHom i '' (s i : Set (R i))
  have hT : T.Finite := Set.finite_iUnion fun i => (s i).finite_toSet.image _
  let D : Subalgebra A (⨂[A] i, R i) := Algebra.adjoin A T
  have hsingle (i : ι) (x : R i) : singleAlgHom i x ∈ D := by
    have hle : Algebra.adjoin A (s i : Set (R i)) ≤ D.comap (singleAlgHom i) := by
      apply Algebra.adjoin_le
      intro a ha
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩)
    rw [hs i] at hle
    exact hle (by trivial)
  refine ⟨hT.toFinset, ?_⟩
  rw [hT.coe_toFinset]
  apply top_unique
  intro x hx
  clear hx
  change x ∈ D
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      apply D.smul_mem
      rw [tprod_eq_prod_single]
      exact D.prod_mem fun i _ => hsingle i (x i)
  | add x y hx hy => exact D.add_mem hx hy

end PiTensorProduct

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Topology
noncomputable section

namespace Algebra.RationalPrincipalOpen

variable {K B : Type*} [Field K] [IsAlgClosed K]
  [CommRing B] [Algebra K B] [Algebra.FiniteType K B]

/-- Every nonempty principal open in a closed irreducible affine subset contains
a rational point, including for nonreduced finite-type algebras. -/
theorem exists_algHom (q : PrimeSpectrum B) (s : B) (hs : s ∉ q.asIdeal) :
    ∃ e : B →ₐ[K] K, q.asIdeal ≤ RingHom.ker e.toRingHom ∧ e s ≠ 0 := by
  letI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := K)
  have hj : q.asIdeal.jacobson = q.asIdeal :=
    IsJacobsonRing.out inferInstance q.isPrime.isRadical
  have hm : ∃ m : Ideal B, q.asIdeal ≤ m ∧ m.IsMaximal ∧ s ∉ m := by
    by_contra! h
    apply hs
    rw [← hj, Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    exact h m hm.1 hm.2
  obtain ⟨m, hqm, hm, hsm⟩ := hm
  letI : m.IsMaximal := hm
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  let E : K ≃ₐ[K] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : B →ₐ[K] K := E.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m)
  refine ⟨e, ?_, ?_⟩
  · intro b hb
    change E.symm (Ideal.Quotient.mk m b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hqm hb), map_zero]
  · intro h
    apply hsm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply E.symm.injective
    simpa [e] using h

/-- A rational point lying over an evaluation ideal has the prescribed coefficient values. -/
theorem restriction_eq_eval {σ : Type*} [Algebra (MvPolynomial σ K) B]
    [IsScalarTower K (MvPolynomial σ K) B]
    (q : PrimeSpectrum B) (c : σ → K)
    (hq : PrimeSpectrum.comap (algebraMap (MvPolynomial σ K) B) q =
      MvPolynomial.pointToPoint (k := K) c)
    (e : B →ₐ[K] K) (he : q.asIdeal ≤ RingHom.ker e.toRingHom) :
    ∀ Q : MvPolynomial σ K,
      e (algebraMap (MvPolynomial σ K) B Q) = MvPolynomial.eval c Q := by
  intro Q
  have hmem : Q - MvPolynomial.C (MvPolynomial.eval c Q) ∈
      (MvPolynomial.pointToPoint (k := K) c).asIdeal := by
    change _ ∈ MvPolynomial.vanishingIdeal K {c}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [← hq] at hmem
  have hzero := he hmem
  change e (algebraMap (MvPolynomial σ K) B
    (Q - MvPolynomial.C (MvPolynomial.eval c Q))) = 0 at hzero
  rw [map_sub, map_sub] at hzero
  have hc (a : K) :
      e (algebraMap (MvPolynomial σ K) B (MvPolynomial.C a)) = a := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K
      (MvPolynomial σ K) B]
    exact e.commutes a
  rw [hc] at hzero
  exact sub_eq_zero.mp hzero

/-- An open affine map carries a nonvanishing rational point to an open set
whose rational fibers retain a nonvanishing rational point. -/
theorem open_specialization {σ : Type*} [Algebra (MvPolynomial σ K) B]
    [IsScalarTower K (MvPolynomial σ K) B]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap (MvPolynomial σ K) B)))
    (c₀ : σ → K) (e₀ : B →ₐ[K] K)
    (h₀ : ∀ Q : MvPolynomial σ K,
      e₀ (algebraMap (MvPolynomial σ K) B Q) = MvPolynomial.eval c₀ Q)
    (s : B) (hs : e₀ s ≠ 0) :
    ∃ U : Set (PrimeSpectrum (MvPolynomial σ K)), IsOpen U ∧
      MvPolynomial.pointToPoint (k := K) c₀ ∈ U ∧
      ∀ c : σ → K, MvPolynomial.pointToPoint (k := K) c ∈ U →
        ∃ e : B →ₐ[K] K,
          (∀ Q : MvPolynomial σ K,
            e (algebraMap (MvPolynomial σ K) B Q) = MvPolynomial.eval c Q) ∧
          e s ≠ 0 := by
  let f := PrimeSpectrum.comap (algebraMap (MvPolynomial σ K) B)
  let U := f '' (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum B))
  refine ⟨U, hopen _ (PrimeSpectrum.basicOpen s).isOpen, ?_, ?_⟩
  · let q₀ : PrimeSpectrum B := ⟨RingHom.ker e₀.toRingHom, RingHom.ker_isPrime _⟩
    refine ⟨q₀, hs, ?_⟩
    apply PrimeSpectrum.ext
    ext Q
    change e₀ (algebraMap (MvPolynomial σ K) B Q) = 0 ↔
      Q ∈ MvPolynomial.vanishingIdeal K {c₀}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, h₀]
    rfl
  · intro c hc
    obtain ⟨q, hqs, hqc⟩ := hc
    obtain ⟨e, he, hes⟩ := exists_algHom (K := K) q s hqs
    exact ⟨e, restriction_eq_eval q c hqc e he, hes⟩

end Algebra.RationalPrincipalOpen

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators TensorProduct Topology
noncomputable section

namespace Algebra

/-- All simultaneous algebraic-specialization steps, conditional only on
openness of the structure map of the finite tensor product. -/
theorem simultaneous_specialization_of_tensor_open
    (K : Type*) [Field K] [IsAlgClosed K]
    (σ ι : Type*) [Finite σ] [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, Algebra (MvPolynomial σ K) (R i)]
    [∀ i, IsScalarTower K (MvPolynomial σ K) (R i)]
    [∀ i, Algebra.FiniteType (MvPolynomial σ K) (R i)]
    (hopen : IsOpenMap (PrimeSpectrum.comap
      (algebraMap (MvPolynomial σ K) (⨂[MvPolynomial σ K] i, R i))))
    (c₀ : σ → K) (e₀ : ∀ i, R i →ₐ[K] K)
    (h₀ : ∀ i (Q : MvPolynomial σ K),
      e₀ i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c₀ Q)
    (P : MvPolynomial (Σ i, R i) K)
    (hP : MvPolynomial.eval (fun t => e₀ t.1 t.2) P ≠ 0) :
    ∃ U : Set (PrimeSpectrum (MvPolynomial σ K)), IsOpen U ∧
      MvPolynomial.pointToPoint (k := K) c₀ ∈ U ∧
      ∀ c : σ → K, MvPolynomial.pointToPoint (k := K) c ∈ U →
        ∃ e : ∀ i, R i →ₐ[K] K,
          (∀ i (Q : MvPolynomial σ K),
            e i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c Q) ∧
          MvPolynomial.eval (fun t => e t.1 t.2) P ≠ 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let A := MvPolynomial σ K
  let B := ⨂[A] i, R i
  letI : Algebra.FiniteType A B := PiTensorProduct.finiteType_family
  letI : Algebra.FiniteType K B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K A) (inferInstance : Algebra.FiniteType A B)
  let j (i : ι) : R i →ₐ[K] B := (PiTensorProduct.singleAlgHom i).restrictScalars K
  let p : B := MvPolynomial.aeval (fun t : Σ i, R i => j t.1 t.2) P
  have heval (e : B →ₐ[K] K) :
      e p = MvPolynomial.eval (fun t : Σ i, R i => e (j t.1 t.2)) P := by
    have heq : e.comp (MvPolynomial.aeval (fun t : Σ i, R i => j t.1 t.2)) =
        MvPolynomial.aeval (fun t : Σ i, R i => e (j t.1 t.2)) := by
      ext t
      simp
    exact DFunLike.congr_fun heq P
  letI : Algebra A K := (MvPolynomial.eval c₀).toAlgebra
  letI : IsScalarTower K A K := IsScalarTower.of_algebraMap_eq fun a => by
    change a = MvPolynomial.eval c₀ (MvPolynomial.C a)
    simp
  let eA (i : ι) : R i →ₐ[A] K :=
    { (e₀ i).toRingHom with commutes' := h₀ i }
  let eB : B →ₐ[K] K := (PiTensorProduct.familyLift eA).restrictScalars K
  have heB (i : ι) (r : R i) : eB (j i r) = e₀ i r := by
    exact PiTensorProduct.familyLift_single eA i r
  have heBcoeff (Q : A) : eB (algebraMap A B Q) = MvPolynomial.eval c₀ Q :=
    (PiTensorProduct.familyLift eA).commutes Q
  have hep : eB p ≠ 0 := by
    rw [heval]
    simpa only [heB] using hP
  obtain ⟨U, hU, hc₀, hspec⟩ :=
    RationalPrincipalOpen.open_specialization hopen c₀ eB heBcoeff p hep
  refine ⟨U, hU, hc₀, ?_⟩
  intro c hc
  obtain ⟨e, he, hpe⟩ := hspec c hc
  refine ⟨fun i => e.comp (j i), ?_, ?_⟩
  · intro i Q
    change e (PiTensorProduct.singleAlgHom i (algebraMap A (R i) Q)) = _
    rw [(PiTensorProduct.singleAlgHom i).commutes Q]
    exact he Q
  · rw [heval] at hpe
    exact hpe

end Algebra

end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators TensorProduct Topology

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K]
    (σ ι : Type*) [Finite σ] [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, Algebra (MvPolynomial σ K) (R i)]
    [∀ i, IsScalarTower K (MvPolynomial σ K) (R i)]
    [∀ i, Algebra.FiniteType (MvPolynomial σ K) (R i)]
    (hopen : ∀ i, IsOpenMap
      (PrimeSpectrum.comap (algebraMap (MvPolynomial σ K) (R i))))
    (hquasi : ∀ i, Algebra.QuasiFinite (MvPolynomial σ K) (R i))
    (c₀ : σ → K) (e₀ : ∀ i, R i →ₐ[K] K)
    (h₀ : ∀ i (Q : MvPolynomial σ K),
      e₀ i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c₀ Q)
    (P : MvPolynomial (Σ i, R i) K)
    (hP : MvPolynomial.eval (fun t => e₀ t.1 t.2) P ≠ 0) :
    ∃ U : Set (PrimeSpectrum (MvPolynomial σ K)), IsOpen U ∧
      MvPolynomial.pointToPoint (k := K) c₀ ∈ U ∧
      ∀ c : σ → K, MvPolynomial.pointToPoint (k := K) c ∈ U →
        ∃ e : ∀ i, R i →ₐ[K] K,
          (∀ i (Q : MvPolynomial σ K),
            e i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c Q) ∧
          MvPolynomial.eval (fun t => e t.1 t.2) P ≠ 0 := by
  letI : IsIntegrallyClosed (MvPolynomial σ K) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have ht := PiTensorProduct.isOpenMap_comap_of_quasiFinite
    (MvPolynomial σ K) ι R hopen hquasi
  exact Algebra.simultaneous_specialization_of_tensor_open K σ ι R ht c₀ e₀ h₀ P hP
