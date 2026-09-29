-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/92eec57a-f731-5898-b9d1-4bf84f9b8855

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace GeomIntegralOfIsAlgClosed

variable {K : Type u} [Field K]

theorem algebraMap_quotient_bijective_of_isAlgClosed [IsAlgClosed K] {A : Type*} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Bijective (algebraMap K (A ⧸ m)) := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

variable (K) in

noncomputable def pointOfMaximal [IsAlgClosed K] {A : Type*} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] : A →ₐ[K] K :=
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective_of_isAlgClosed m)
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      exact e.symm_apply_apply k }

theorem pointOfMaximal_eq_zero_iff [IsAlgClosed K] {A : Type*} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] (a : A) :
    pointOfMaximal K m a = 0 ↔ a ∈ m := by
  change (RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective_of_isAlgClosed m)).symm (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem isDomain_tensorProduct_of_isAlgClosed [IsAlgClosed K] (A B : Type u) [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] [IsDomain A] [CommRing B] [Algebra K B] [IsDomain B] :
    IsDomain (A ⊗[K] B) := by
  classical
  haveI : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective

  let bB := Module.Free.chooseBasis K B
  let 𝔅 := Algebra.TensorProduct.basis A bB
  let I : A ⊗[K] B → Ideal A := fun x => Ideal.span (Set.range (𝔅.repr x))
  have hI : ∀ x, I x = ⊥ → x = 0 := by
    intro x hx
    apply 𝔅.repr.injective
    rw [map_zero]
    ext i
    exact (Ideal.span_eq_bot.mp hx) _ ⟨i, rfl⟩

  have hpt : ∀ (x y : A ⊗[K] B), x * y = 0 → ∀ (m : Ideal A) [m.IsMaximal], I x ≤ m ∨ I y ≤ m := by
    intro x y hxy m _
    let φ : A →ₐ[K] K := pointOfMaximal K m
    let ψ : A ⊗[K] B →ₐ[K] B :=
      Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B)
        (fun _ _ => Commute.all _ _)
    have hψ : ∀ (z : A ⊗[K] B) (i), bB.repr (ψ z) i = φ (𝔅.repr z i) := by
      intro z i
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [ψ, 𝔅, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
          Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.TensorProduct.basis_repr_tmul,
          Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
          RingHom.id_apply]
      | add z w hz hw => simp [map_add, hz, hw]
    have hker : ∀ z : A ⊗[K] B, ψ z = 0 → I z ≤ m := by
      intro z hz
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, ← pointOfMaximal_eq_zero_iff (K := K), ← hψ, hz, map_zero,
        Finsupp.zero_apply]
    have h0 : ψ x * ψ y = 0 := by rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (hker x h)
    · exact Or.inr (hker y h)

  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K) (B := A)
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  have hle : I x * I y ≤ (⊥ : Ideal A) := by
    rw [← Ideal.radical_bot_of_noZeroDivisors, Ideal.radical_eq_jacobson]
    refine le_sInf ?_
    rintro J ⟨-, hJ⟩
    rcases hpt x y hxy J with h | h
    · exact Ideal.mul_le_left.trans h
    · exact Ideal.mul_le_right.trans h
  rcases (Ideal.mul_eq_bot.mp (le_bot_iff.mp hle)) with h | h
  · exact Or.inl (hI x h)
  · exact Or.inr (hI y h)

theorem isIntegral_pullback_SpecMap_of_isAlgClosed [IsAlgClosed K] {A : CommRingCat.{u}}
    (φ : CommRingCat.of K ⟶ A) [IsIntegral (Spec A)] [LocallyOfFiniteType (Spec.map φ)]
    (K' : Type u) [Field K'] [Algebra K K'] :
    IsIntegral ↑(pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap K K')))) := by
  algebraize [φ.hom]
  have hft : Algebra.FiniteType K A := by
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp ‹_›
    exact RingHom.finiteType_algebraMap.mp this
  have : IsDomain A := (affine_isIntegral_iff A).mp ‹_›
  have : IsDomain (A ⊗[K] K') := isDomain_tensorProduct_of_isAlgClosed A K'
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ≅
      Spec (.of (A ⊗[K] K')) :=
    pullbackSpecIso K A K'
  exact IsIntegral.of_isIso e.inv

end GeomIntegralOfIsAlgClosed

open GeomIntegralOfIsAlgClosed in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by
  refine ⟨(geometrically_iff_of_commRing (P := fun Y : Scheme.{u} => IsIntegral Y)).mpr ?_⟩
  intro K' _ _ Y fst snd h
  let i : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  suffices hP : IsIntegral ↑(pullback f i) by
    haveI := hP
    exact IsIntegral.of_isIso h.isoPullback.inv
  let 𝒰 := X.affineCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 f i

  have hint : ∀ j, Nonempty (𝒰.X j) → IsIntegral (𝒱.X j) := by
    intro j hj

    have hI : IsIntegral (𝒰.X j) := isIntegral_of_isOpenImmersion (𝒰.f j)
    have hlft : LocallyOfFiniteType (𝒰.f j ≫ f) := inferInstance
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒰.f j ≫ f)
    have hP := @isIntegral_pullback_SpecMap_of_isAlgClosed K _ _ _ φ hI (hφ ▸ hlft) K' _ _
    let e : pullback (Spec.map φ) i ≅ pullback (𝒰.f j ≫ f) i := pullback.congrHom hφ rfl
    haveI := hP
    exact IsIntegral.of_isIso e.hom

  have hred : ∀ j, IsReduced (𝒱.X j) := by
    intro j
    rcases isEmpty_or_nonempty (𝒰.X j) with hj | hj
    · have : IsEmpty ↑(pullback (𝒰.f j ≫ f) i) := Function.isEmpty (pullback.fst (𝒰.f j ≫ f) i)
      have : IsReduced (𝒰.X j) := isReduced_of_isOpenImmersion (𝒰.f j)
      exact isReduced_of_isOpenImmersion (pullback.fst (𝒰.f j ≫ f) i)
    · haveI := hint j hj
      infer_instance
  haveI : IsReduced ↑(pullback f i) := IsReduced.of_openCover _ 𝒱

  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  haveI hj₀ : Nonempty (𝒰.X (𝒰.idx x₀)) := let ⟨y, _⟩ := 𝒰.covers x₀; ⟨y⟩
  haveI := hint _ hj₀
  have hrange : Set.range (𝒱.f (𝒰.idx x₀)) =
      pullback.fst f i ⁻¹' Set.range (𝒰.f (𝒰.idx x₀)) := by
    have hid : Set.range (𝟙 (Spec (.of K')) : Spec (.of K') ⟶ _) = Set.univ :=
      Set.range_eq_univ.mpr fun y => ⟨y, rfl⟩
    have := Scheme.Pullback.range_map (𝒰.f (𝒰.idx x₀) ≫ f) i f i (𝒰.f (𝒰.idx x₀)) (𝟙 _)
      (𝟙 _) (by simp) (by simp)
    rw [hid, Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hopen : IsOpenMap (pullback.fst f i) := (pullback.fst f i).isOpenMap
  have hdense : Dense (Set.range (𝒱.f (𝒰.idx x₀))) := by
    rw [hrange, dense_iff_inter_open]
    intro W hW hWne
    obtain ⟨_, ⟨w, hw, rfl⟩, hw'⟩ := nonempty_preirreducible_inter (hopen W hW)
      (𝒰.f (𝒰.idx x₀)).isOpenEmbedding.isOpen_range (hWne.image _) (Set.range_nonempty _)
    exact ⟨w, hw, hw'⟩
  have hirr : IsIrreducible (Set.range (𝒱.f (𝒰.idx x₀))) := by
    have := (IrreducibleSpace.isIrreducible_univ (X := 𝒱.X (𝒰.idx x₀))).image _
      (𝒱.f (𝒰.idx x₀)).continuous.continuousOn
    rwa [Set.image_univ] at this
  haveI : IrreducibleSpace ↑(pullback f i) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense.closure_eq]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed (solution)
