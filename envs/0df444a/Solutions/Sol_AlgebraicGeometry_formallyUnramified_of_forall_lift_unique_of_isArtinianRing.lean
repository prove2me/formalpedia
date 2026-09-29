-- Prove2me | solution 1 for AlgebraicGeometry.formallyUnramified_of_forall_lift_unique_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ef79dc5b-ccee-5d55-a8f2-d7e8c8a3d005

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

set_option autoImplicit false

open TensorProduct

namespace E3bU

theorem exists_linearMap_ne_zero_of_nontrivial {S k M : Type u} [CommRing S] [Field k] [Algebra S k]
    [AddCommGroup M] [Module S M] (h : Nontrivial (k ⊗[S] M)) :
    ∃ ψ : M →ₗ[S] k, ψ ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : k ⊗[S] M)
  obtain ⟨f, hf⟩ := not_forall.mp ((Module.forall_dual_apply_eq_zero_iff k v).not.mpr hv)
  refine ⟨(LinearMap.restrictScalars S (f : k ⊗[S] M →ₗ[k] k)).comp (TensorProduct.mk S k M 1), fun H => hf ?_⟩
  have hzero : ∀ x : M, f ((1 : k) ⊗ₜ[S] x) = 0 := fun x =>
    LinearMap.congr_fun H x
  have : f = 0 := by
    refine LinearMap.ext fun w => ?_
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, LinearMap.zero_apply]
    | tmul c x =>
      have : c ⊗ₜ[S] x = c • ((1 : k) ⊗ₜ[S] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, hzero, smul_zero, LinearMap.zero_apply]
    | add a b ha hb => rw [map_add, ha, hb, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, add_zero]
  rw [this, LinearMap.zero_apply]

theorem formallyUnramified_of_forall_derivation_eq_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
      (D : Derivation R S K), D = 0) :
    Algebra.FormallyUnramified R S := by
  classical

  suffices hs : Subsingleton Ω[S⁄R] from ⟨hs⟩
  rw [← Module.support_eq_empty_iff (R := S), Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq

  obtain ⟨ψ₀, hψ₀⟩ := exists_linearMap_ne_zero_of_nontrivial hq

  let k := q.asIdeal.ResidueField
  let K := AlgebraicClosure k
  let ι : k →ₗ[S] K := (IsScalarTower.toAlgHom S k K).toLinearMap
  have hι : Function.Injective ι := (algebraMap k K).injective
  let ψ : Ω[S⁄R] →ₗ[S] K := ι.comp ψ₀
  have hψ : ψ ≠ 0 := fun h0 => hψ₀ (by
    refine LinearMap.ext fun x => hι ?_
    have := LinearMap.congr_fun h0 x
    simpa [ψ] using this)

  have hD := H K ((KaehlerDifferential.linearMapEquivDerivation R S) ψ)
  apply hψ
  have := congrArg (KaehlerDifferential.linearMapEquivDerivation R S).symm hD
  rwa [LinearEquiv.symm_apply_apply, map_zero] at this

end E3bU

namespace E3bU

open TrivSqZeroExt

section DualNumbers

variable {S K : Type u} [CommRing S] [Field K] [Algebra S K]

def liftOfDerivation {R : Type u} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R S K]
    (D : Derivation R S K) : S →+* TrivSqZeroExt K K where
  toFun s := inl (algebraMap S K s) + inr (D s)
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp [Derivation.map_one_eq_zero]
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [Derivation.leibniz, map_mul, snd_add, snd_inl, snd_inr, zero_add, snd_mul, fst_add, fst_inl,
        fst_inr, add_zero, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Algebra.smul_def,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp

theorem fst_liftOfDerivation {R : Type u} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R S K]
    (D : Derivation R S K) (s : S) : (liftOfDerivation D s).fst = algebraMap S K s := by
  simp [liftOfDerivation]

theorem snd_liftOfDerivation {R : Type u} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R S K]
    (D : Derivation R S K) (s : S) : (liftOfDerivation D s).snd = D s := by
  simp [liftOfDerivation]

theorem liftOfDerivation_algebraMap {R : Type u} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R S K]
    (D : Derivation R S K) (r : R) : liftOfDerivation D (algebraMap R S r) = inl (algebraMap R K r) := by
  apply TrivSqZeroExt.ext
  · simp [liftOfDerivation, ← IsScalarTower.algebraMap_apply]
  · simp [liftOfDerivation, Derivation.map_algebraMap]

def lift₀ (S K : Type u) [CommRing S] [Field K] [Algebra S K] : S →+* TrivSqZeroExt K K :=
  (inlHom K K).comp (algebraMap S K)

theorem eq_zero_of_liftOfDerivation_eq {R : Type u} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R S K]
    (D : Derivation R S K) (h : liftOfDerivation D = lift₀ S K) : D = 0 := by
  refine Derivation.ext fun s => ?_
  have := congrArg (fun f : S →+* TrivSqZeroExt K K => (f s).snd) h
  simpa [snd_liftOfDerivation, lift₀] using this

theorem fstHom_surjective : Function.Surjective (fstHom K K K).toRingHom :=
  fun x => ⟨inl x, by simp⟩

theorem mem_maximalIdeal_iff (x : TrivSqZeroExt K K) : x ∈ IsLocalRing.maximalIdeal (TrivSqZeroExt K K) ↔ x.fst = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not]

theorem ker_fstHom_mul_maximalIdeal :
    RingHom.ker (fstHom K K K).toRingHom * IsLocalRing.maximalIdeal (TrivSqZeroExt K K) = ⊥ := by
  refine le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)
  rw [RingHom.mem_ker] at hr
  rw [mem_maximalIdeal_iff] at hs
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext
  · simp [hs]
  · change r.fst = 0 at hr
    simp [snd_mul, hr, hs]

scoped instance : IsArtinianRing (TrivSqZeroExt K K) :=
  haveI : Module.Finite K (TrivSqZeroExt K K) := inferInstanceAs (Module.Finite K (K × K))
  IsArtinianRing.of_finite K _

noncomputable def residueEquiv : K ≃+* IsLocalRing.ResidueField (TrivSqZeroExt K K) :=
  RingEquiv.ofBijective ((IsLocalRing.residue (TrivSqZeroExt K K)).comp (algebraMap K (TrivSqZeroExt K K)))
    ⟨RingHom.injective _, fun y => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨x.fst, ?_⟩
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal (TrivSqZeroExt K K)) (algebraMap K (TrivSqZeroExt K K) x.fst) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (TrivSqZeroExt K K)) x
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_maximalIdeal_iff]
      simp [TrivSqZeroExt.algebraMap_eq_inl]⟩

scoped instance [IsAlgClosed K] : IsAlgClosed (IsLocalRing.ResidueField (TrivSqZeroExt K K)) :=
  IsAlgClosed.of_ringEquiv K _ residueEquiv

end DualNumbers

end E3bU
p2m_reactivate "P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing.E3bU"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
theorem solution
    {R : Type u} [CommRing R] {M : Scheme.{u}} (ϖ : M ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∀ m₁ m₂ : Spec (CommRingCat.of T') ⟶ M, m₁ ≫ ϖ = s → Spec.map (CommRingCat.ofHom p) ≫ m₁ = m →
          m₂ ≫ ϖ = s → Spec.map (CommRingCat.ofHom p) ≫ m₂ = m → m₁ = m₂) :
    FormallyUnramified ϖ := by
  classical

  wlog hM : ∃ S : CommRingCat.{u}, M = Spec S generalizing M
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) M.affineCover]
    intro i
    refine this (M.affineCover.f i ≫ ϖ) ?_ ⟨_, rfl⟩
    intro T' T _ _ _ _ _ _ p hp hsmall s m hm m₁ m₂ h1 h1' h2 h2'
    have key := h T' T p hp hsmall s (m ≫ M.affineCover.f i) (by rw [Category.assoc, hm])
      (m₁ ≫ M.affineCover.f i) (m₂ ≫ M.affineCover.f i)
      (by rw [Category.assoc, h1]) (by rw [← Category.assoc, h1']) (by rw [Category.assoc, h2]) (by rw [← Category.assoc, h2'])
    exact (cancel_mono (M.affineCover.f i)).mp key
  obtain ⟨S, rfl⟩ := hM
  obtain ⟨φ, rfl⟩ : ∃ φ, ϖ = Spec.map φ := ⟨_, (Spec.map_preimage ϖ).symm⟩
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  algebraize [φ.hom]
  refine E3bU.formallyUnramified_of_forall_derivation_eq_zero (fun K _ _ _ _ _ D => ?_)
  apply E3bU.eq_zero_of_liftOfDerivation_eq D

  have e0 : φ ≫ CommRingCat.ofHom (algebraMap S K) =
      CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K K)).comp (algebraMap R K)) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom := by
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl]
    show algebraMap S K (algebraMap R S x) = (TrivSqZeroExt.inl (algebraMap R K x) : TrivSqZeroExt K K).fst
    rw [TrivSqZeroExt.fst_inl, ← IsScalarTower.algebraMap_apply]
  have e1 : φ ≫ CommRingCat.ofHom (E3bU.liftOfDerivation D) =
      CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K K)).comp (algebraMap R K)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl]
    exact E3bU.liftOfDerivation_algebraMap D x
  have e1' : CommRingCat.ofHom (E3bU.liftOfDerivation D) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
      CommRingCat.ofHom (algebraMap S K) := by
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact E3bU.fst_liftOfDerivation D x
  have e2 : φ ≫ CommRingCat.ofHom (E3bU.lift₀ S K) =
      CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K K)).comp (algebraMap R K)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl,
      E3bU.lift₀, TrivSqZeroExt.inlHom_apply]
    show TrivSqZeroExt.inl (algebraMap S K (algebraMap R S x)) = _
    rw [← IsScalarTower.algebraMap_apply]
  have e2' : CommRingCat.ofHom (E3bU.lift₀ S K) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
      CommRingCat.ofHom (algebraMap S K) := by
    ext x
    simp [E3bU.lift₀]
  have key := h (TrivSqZeroExt K K) K (TrivSqZeroExt.fstHom K K K).toRingHom E3bU.fstHom_surjective
    E3bU.ker_fstHom_mul_maximalIdeal
    (Spec.map (CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K K)).comp (algebraMap R K))))
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (by rw [← Spec.map_comp, e0, Spec.map_comp])
    (Spec.map (CommRingCat.ofHom (E3bU.liftOfDerivation D))) (Spec.map (CommRingCat.ofHom (E3bU.lift₀ S K)))
    (by rw [← Spec.map_comp, e1]) (by rw [← Spec.map_comp, e1'])
    (by rw [← Spec.map_comp, e2]) (by rw [← Spec.map_comp, e2'])
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  simpa using this

end S_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing
end P2MW
export P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing (solution)
