-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:51.058891+00:00
-- url     : https://prove2.me/theorems/c49e0107-6a69-44d6-ba9d-e2123147ace3
-- title:
--   Jacobian Criterion
-- statement:
--   Definitions and structural lemmas for Jacobian Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
namespace JacobianCriterion
section
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra (MvPolynomial ι k) S]
noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)
end
section
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
theorem linearIndependent_one_tmul_D_X :
    LinearIndependent S fun i : ι =>
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i)) := by
  have hfun : (fun i : ι => (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))) =
      ⇑(Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis k ι)) := by
    funext i
    rw [Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  rw [hfun]
  exact (Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).linearIndependent
theorem D_mem_span_range_D_X (K : Type*) [CommRing K] (σ : Type*)
    (f : MvPolynomial σ K) :
    KaehlerDifferential.D K (MvPolynomial σ K) f ∈
      Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X i)) := by
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]
    exact Submodule.zero_mem _
  · rename_i p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · rename_i p i hp
    rw [Derivation.leibniz]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.smul_mem _ _ hp)
theorem span_range_D_X_eq_top (K : Type*) [CommRing K] (σ : Type*) :
    Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X i)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact D_mem_span_range_D_X K σ f
theorem smul_one_tmul
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (a : A) (m : M) :
    a • ((1 : A) ⊗ₜ[R] m) = a ⊗ₜ[R] m := by
  have h2 : a • (1 : A) = a := by rw [smul_eq_mul, mul_one]
  have h1 : ((a • (1 : A)) ⊗ₜ[R] m : A ⊗[R] M) = a • ((1 : A) ⊗ₜ[R] m) := by
    rw [TensorProduct.smul_tmul']
  rw [h2] at h1
  exact h1.symm
theorem top_le_span_range_one_tmul
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M]
    (τ : Type*) (g : τ → M)
    (hs : Submodule.span R (Set.range g) = ⊤) :
    ⊤ ≤ Submodule.span A (Set.range fun i : τ => (1 : A) ⊗ₜ[R] g i) := by
  have key : ∀ m : M, ∀ a : A,
      a ⊗ₜ[R] m ∈ Submodule.span A (Set.range fun i : τ => (1 : A) ⊗ₜ[R] g i) := by
    intro m
    have hm : m ∈ Submodule.span R (Set.range g) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · rintro x ⟨i, rfl⟩ a
      rw [← smul_one_tmul R A M a (g i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro a
      rw [TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy a
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hx a) (hy a)
    · intro r x _ hx a
      have e : a ⊗ₜ[R] (r • x) = (r • a) ⊗ₜ[R] x := by
        rw [TensorProduct.smul_tmul]
      rw [e]
      exact hx (r • a)
  intro w _
  refine TensorProduct.induction_on w ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro a m
    exact key m a
  · intro u v hu hv
    exact Submodule.add_mem _ hu hv
omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
theorem top_le_span_one_tmul_D_X :
    ⊤ ≤ Submodule.span S (Set.range fun i : ι =>
        (1 : S) ⊗ₜ[MvPolynomial ι k]
          (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))) :=
  top_le_span_range_one_tmul (MvPolynomial ι k) S (KaehlerDifferential k (MvPolynomial ι k)) ι
    (fun i : ι => KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))
    (span_range_D_X_eq_top k ι)
noncomputable def tensorKaehlerBasis :
    Module.Basis ι S (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) :=
  Module.Basis.mk (linearIndependent_one_tmul_D_X k ι S) (top_le_span_one_tmul_D_X k ι S)
end
section
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
omit [IsScalarTower k (MvPolynomial ι k) S] in
theorem linearIndependent_D_coord_of_isUnit_det (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    LinearIndependent S fun i : ι => KaehlerDifferential.D k S (coord k ι S i) :=
  (b.is_basis_iff_det.mpr h).1
omit [IsScalarTower k (MvPolynomial ι k) S] in
theorem top_le_span_D_coord_of_isUnit_det (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    ⊤ ≤ Submodule.span S
        (Set.range fun i : ι => KaehlerDifferential.D k S (coord k ι S i)) := by
  have hb := b.is_basis_iff_det.mpr h
  have h2 : Submodule.span S
      (Set.range fun i : ι => KaehlerDifferential.D k S (coord k ι S i)) = ⊤ := hb.2
  exact h2.ge
noncomputable def coordBasis (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Module.Basis ι S (KaehlerDifferential k S) :=
  Module.Basis.mk (linearIndependent_D_coord_of_isUnit_det k ι S b h) (top_le_span_D_coord_of_isUnit_det k ι S b h)
end
section
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] [Algebra k S]
variable (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [Algebra.FormallyEtale S S']
theorem linearIndependent_kaehlerMap_basis
    (b : Module.Basis ι S (KaehlerDifferential k S)) :
    LinearIndependent S' fun i : ι => KaehlerDifferential.map k k S S' (b i) := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k S S'
  have hfun : (fun i : ι => KaehlerDifferential.map k k S S' (b i)) =
      ⇑((Algebra.TensorProduct.basis S' b).map hbc.equiv) := by
    funext i
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, hbc.equiv_tmul, one_smul]
  rw [hfun]
  exact ((Algebra.TensorProduct.basis S' b).map hbc.equiv).linearIndependent
theorem top_le_span_kaehlerMap_basis (b : Module.Basis ι S (KaehlerDifferential k S)) :
    ⊤ ≤ Submodule.span S'
        (Set.range fun i : ι => KaehlerDifferential.map k k S S' (b i)) := by
  have hsub : Subsingleton (KaehlerDifferential S S') :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hexact := KaehlerDifferential.exact_mapBaseChange_map k S S'
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k S S') := by
    intro x
    obtain ⟨y, hy⟩ := (hexact x).mp (Subsingleton.elim _ _)
    exact ⟨y, hy⟩
  have hspan : ⊤ ≤ Submodule.span S' (Set.range fun i : ι => (1 : S') ⊗ₜ[S] b i) :=
    top_le_span_range_one_tmul S S' (KaehlerDifferential k S) ι (⇑b) b.span_eq
  have hle : Submodule.span S' (Set.range fun i : ι => (1 : S') ⊗ₜ[S] b i) ≤
      Submodule.comap (KaehlerDifferential.mapBaseChange k S S')
        (Submodule.span S'
          (Set.range fun i : ι => KaehlerDifferential.map k k S S' (b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : KaehlerDifferential.mapBaseChange k S S' ((1 : S') ⊗ₜ[S] b i) ∈
        Submodule.span S'
          (Set.range fun j : ι => KaehlerDifferential.map k k S S' (b j)) := by
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact h1
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hspan Submodule.mem_top)
noncomputable def inducedBasis (b : Module.Basis ι S (KaehlerDifferential k S)) :
    Module.Basis ι S' (KaehlerDifferential k S') :=
  Module.Basis.mk (linearIndependent_kaehlerMap_basis k ι S S' b) (top_le_span_kaehlerMap_basis k ι S S' b)
end
end JacobianCriterion
end FunctorialResolution.EmbeddedResolution


