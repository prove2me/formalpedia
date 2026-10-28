-- Prove2me | solution 1 for AlgebraicGeometry.exists_finite_extension_with_distinct_sections_of_positive_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T18:29:45.326973+00:00
-- url     : https://prove2.me/submissions/c01e5cab-3fe0-4636-8ecd-dc88d42e4fb5

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u v

namespace PhilipponFiniteMarkedPoints

lemma infinite_closedPoints_of_positive_dimension
    (X : Type u) [TopologicalSpace X] [JacobsonSpace X]
    (hX : 0 < topologicalKrullDim X) : (closedPoints X).Infinite := by
  intro h
  letI : DiscreteTopology X := JacobsonSpace.discreteTopology h
  exact (not_lt_of_ge (topologicalKrullDim_zero_of_discreteTopology X)) hX

lemma exists_common_finite_extension
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (E : ι → Type u) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, FiniteDimensional K (E i)] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Nonempty (∀ i, E i →ₐ[K] L) := by
  let Ω := AlgebraicClosure K
  let φ : ∀ i, E i →ₐ[K] Ω := fun i => IsAlgClosed.lift
  let R : ι → IntermediateField K Ω := fun i => (φ i).fieldRange
  haveI (i : ι) : FiniteDimensional K (R i) :=
    Module.Finite.equiv (φ i).equivFieldRange.toLinearEquiv
  let L : IntermediateField K Ω := ⨆ i, R i
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_iSup_of_finite
  let ψ : ∀ i, E i →ₐ[K] L := fun i =>
    (IntermediateField.inclusion (le_iSup R i)).comp (φ i).equivFieldRange.toAlgHom
  exact ⟨L, inferInstance, inferInstance, inferInstance, ⟨ψ⟩⟩

lemma finite_residueField_of_closedPoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (Spec.preimage (X.fromSpecResidueField x ≫ π)).hom.toAlgebra
    FiniteDimensional K (X.residueField x) := by
  letI := (Spec.preimage (X.fromSpecResidueField x ≫ π)).hom.toAlgebra
  haveI : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  haveI : IsFinite (X.fromSpecResidueField x ≫ π) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have h := (IsFinite.SpecMap_iff (Spec.preimage (X.fromSpecResidueField x ≫ π))).mp
    (by rw [Spec.map_preimage]; infer_instance)
  exact h

lemma exists_finite_extension_with_sections_of_closedPoints
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (ι : Type v) [Finite ι] (x : ι → X)
    (hx : ∀ i, IsClosed ({x i} : Set X)) (hxi : Function.Injective x) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (σ : ι → (Spec (.of L) ⟶
        pullback π (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      (∀ i, σ i ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        𝟙 (Spec (.of L))) ∧
      (∀ i, IsClosedImmersion (σ i)) ∧
      (∀ i z, pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap K L))) (σ i z) =
        x i) ∧
      Pairwise (fun i j => Disjoint (Set.range (σ i)) (Set.range (σ j))) := by
  classical
  let E : ι → Type u := fun i => X.residueField (x i)
  let φ (i : ι) := Spec.preimage (X.fromSpecResidueField (x i) ≫ π)
  letI (i : ι) : Algebra K (E i) := (φ i).hom.toAlgebra
  haveI (i : ι) : FiniteDimensional K (E i) :=
    finite_residueField_of_closedPoint π (x i) (hx i)
  obtain ⟨L, hL, aL, hfin, ⟨ψ⟩⟩ := exists_common_finite_extension K ι E
  letI := hL
  letI := aL
  letI := hfin
  let β : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let a (i : ι) : Spec (.of L) ⟶ X :=
    Spec.map (CommRingCat.ofHom (ψ i).toRingHom) ≫ X.fromSpecResidueField (x i)
  have ha (i : ι) : a i ≫ π = β := by
    dsimp only [a]
    rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField (x i) ≫ π),
      ← Spec.map_comp]
    congr 1
    ext z
    exact (ψ i).commutes z
  let σ (i : ι) : Spec (.of L) ⟶ pullback π β :=
    pullback.lift (a i) (𝟙 _) (by simpa using ha i)
  have hσ (i : ι) : σ i ≫ pullback.snd π β = 𝟙 _ := pullback.lift_snd _ _ _
  have hpoint (i : ι) (z : Spec (.of L)) : pullback.fst π β (σ i z) = x i := by
    rw [← Scheme.Hom.comp_apply, show σ i ≫ pullback.fst π β = a i from
      pullback.lift_fst _ _ _]
    simp only [a, Scheme.Hom.comp_apply]
    exact X.fromSpecResidueField_apply (x i)
      (Spec.map (CommRingCat.ofHom (ψ i).toRingHom) z)
  refine ⟨L, hL, aL, hfin, σ, hσ, ?_, hpoint, ?_⟩
  · intro i
    exact isClosedImmersion_of_comp_eq_id (pullback.snd π β) (σ i) (hσ i)
  · intro i j hij
    rw [Set.disjoint_range_iff]
    intro z w hzw
    apply hij
    apply hxi
    exact (hpoint i z).symm.trans ((congrArg (pullback.fst π β) hzw).trans (hpoint j w))

theorem exists_finite_extension_with_distinct_sections
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hdim : 0 < topologicalKrullDim X) (n : ℕ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (σ : Fin n → (Spec (.of L) ⟶
        pullback π (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      (∀ i, σ i ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        𝟙 (Spec (.of L))) ∧
      (∀ i, IsClosedImmersion (σ i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (σ i)) (Set.range (σ j))) := by
  classical
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  let e : ℕ ↪ closedPoints X :=
    (infinite_closedPoints_of_positive_dimension X hdim).natEmbedding _
  let x : Fin n → X := fun i => (e i.val).val
  have hx (i : Fin n) : IsClosed ({x i} : Set X) := (e i.val).property
  have hxi : Function.Injective x := by
    intro i j hij
    exact Fin.ext (e.injective (Subtype.ext hij))
  obtain ⟨L, hL, aL, hfin, σ, hσ, hclosed, _, hpair⟩ :=
    exists_finite_extension_with_sections_of_closedPoints π (Fin n) x hx hxi
  exact ⟨L, hL, aL, hfin, σ, hσ, hclosed, hpair⟩

end PhilipponFiniteMarkedPoints


theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hdim : 0 < topologicalKrullDim X) (n : ℕ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (σ : Fin n → (Spec (.of L) ⟶
        pullback π (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      (∀ i, σ i ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        𝟙 (Spec (.of L))) ∧
      (∀ i, IsClosedImmersion (σ i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (σ i)) (Set.range (σ j))) := by
  exact PhilipponFiniteMarkedPoints.exists_finite_extension_with_distinct_sections π hdim n
