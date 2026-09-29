-- Prove2me | solution 1 for ArithmeticE.polynomial_relation_basis
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:35:56.423787+00:00
-- url     : https://prove2.me/submissions/08d08874-ac58-4107-b1c2-c7f352fdf949

import Definitions.Def_beukersLiftingData
open scoped BigOperators
open Polynomial
namespace BeukersRelations

lemma kernel_retraction {R M N : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    (L : M →ₗ[R] N) :
    ∃ P : M →ₗ[R] LinearMap.ker L, ∀ x : LinearMap.ker L, P x = x := by
  haveI : Module.Finite R (LinearMap.range L) := Module.Finite.range L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property L.rangeRestrict
    (LinearMap.id : LinearMap.range L →ₗ[R] LinearMap.range L) (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩)
  let P : M →ₗ[R] LinearMap.ker L :=
    (LinearMap.id - s.comp L.rangeRestrict).codRestrict (LinearMap.ker L) (by
      intro x
      change L (x - s (L.rangeRestrict x)) = 0
      have he := DFunLike.congr_fun hs (L.rangeRestrict x)
      have he' := congrArg Subtype.val he
      change L (s (L.rangeRestrict x)) = L x at he'
      simp [he'])
  refine ⟨P, ?_⟩
  intro x
  apply Subtype.ext
  change (x : M) - s (L.rangeRestrict x) = x
  have hx : L.rangeRestrict x = 0 := Subtype.ext x.property
  simp [hx]


noncomputable def relationMap {K : Type*} [Field K] (m : ℕ)
    (f : Fin m → PowerSeries K) : (Fin m → Polynomial K) →ₗ[Polynomial K] PowerSeries K where
  toFun p := ∑ i, (p i : PowerSeries K) * f i
  map_add' p q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    change (∑ i, ((c * p i : Polynomial K) : PowerSeries K) * f i) =
      (c : PowerSeries K) * ∑ i, (p i : PowerSeries K) * f i
    simp [Finset.mul_sum, mul_assoc]

lemma powerSeries_torsion_free {K : Type*} [Field K] :
    Module.IsTorsionFree (Polynomial K) (PowerSeries K) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro p f h
  change (p : PowerSeries K) * f = 0 at h
  rcases mul_eq_zero.mp h with hp | hf
  · left
    exact (Polynomial.coe_injective K) (by simpa using hp)
  · exact Or.inr hf

lemma relation_basis {K : Type*} [Field K] (m : ℕ) (f : Fin m → PowerSeries K) :
    ∃ (r : ℕ) (C : Fin r → Fin m → Polynomial K)
      (U : Fin r → Fin m → Polynomial K),
      (∀ j, ∑ i, (C j i : PowerSeries K) * f i = 0) ∧
      (∀ p : Fin m → Polynomial K, (∑ i, (p i : PowerSeries K) * f i = 0) →
        ∃ b : Fin r → Polynomial K, ∀ i, p i = ∑ j, b j * C j i) ∧
      (∀ j k, ∑ i, U j i * C k i = if j = k then 1 else 0) := by
  classical
  letI := powerSeries_torsion_free (K := K)
  let L := relationMap m f
  obtain ⟨P, hP⟩ := kernel_retraction L
  let r := Module.finrank (Polynomial K) (LinearMap.ker L)
  let b := Module.finBasis (Polynomial K) (LinearMap.ker L)
  let E := Pi.basisFun (Polynomial K) (Fin m)
  let A : (Fin m → Polynomial K) →ₗ[Polynomial K] (Fin r →₀ Polynomial K) :=
    b.repr.toLinearMap.comp P
  refine ⟨r, (fun j => (b j).val), (fun j i => A (E i) j), ?_, ?_, ?_⟩
  · intro j
    exact (b j).property
  · intro p hp
    let x : LinearMap.ker L := ⟨p, hp⟩
    refine ⟨fun j => b.repr x j, ?_⟩
    intro i
    have h := congrArg (fun y : LinearMap.ker L => y.val i) (b.sum_repr x)
    change (∑ j, b.repr x j • b j : LinearMap.ker L).val i = p i at h
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
  · intro j k
    have h := congrArg (fun v : Fin r →₀ Polynomial K => v j)
      (congrArg A (E.sum_repr (b k).val))
    have hab : A (b k).val = Finsupp.single k 1 := by
      change b.repr (P (b k).val) = _
      rw [hP, b.repr_self]
    simpa [map_sum, map_smul, E, hab, mul_comm, eq_comm, Finsupp.single_apply] using h

end BeukersRelations

namespace BeukersRelations
lemma specialize_independent {K : Type*} [Field K] {m r : ℕ}
    (C U : Fin r → Fin m → Polynomial K)
    (hU : ∀ j k, ∑ i, U j i * C k i = if j = k then 1 else 0)
    (ξ : K) : LinearIndependent K (fun j i => (C j i).eval ξ) := by
  classical
  have he : ∀ j k, ∑ i, (U j i).eval ξ * (C k i).eval ξ =
      if j = k then 1 else 0 := by
    intro j k
    simpa only [eval_finset_sum, eval_mul, apply_ite, eval_one, eval_zero] using
      congrArg (fun p : Polynomial K => p.eval ξ) (hU j k)
  rw [Fintype.linearIndependent_iff]
  intro d hd j
  have hd' : ∀ i, ∑ k, d k * (C k i).eval ξ = 0 := by
    intro i
    simpa using congrFun hd i
  calc
    d j = ∑ k, d k * (∑ i, (U j i).eval ξ * (C k i).eval ξ) := by simp [he]
    _ = ∑ i, (U j i).eval ξ * (∑ k, d k * (C k i).eval ξ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by simp [hd']
end BeukersRelations

theorem solution (m : ℕ) (f : Fin m → PowerSeries ℂ) : ArithmeticE.RelationBasis f := by
  exact BeukersRelations.relation_basis m f
#print axioms solution
