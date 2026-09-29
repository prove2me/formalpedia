-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bef8fd4f-9e2e-57b3-8417-18e3eb926660

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_SemistableModel_exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing
import Theorems.Thm_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    [IsAlgClosed (ResidueField A)]
    {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : A, φ (algebraMap L F (algebraMap A L a)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus) :
    ∃ (φT : Polynomial A →+* ↥(SemistableModel.localRing X φ x))
      (χ : ↥(SemistableModel.localRing X φ x) →+* ResidueField A),
      (∀ a : A, algebraMap L F (algebraMap A L a) ∈ SemistableModel.localRing X φ x) ∧
      (∀ a : A, ((φT (Polynomial.C a) : ↥(SemistableModel.localRing X φ x)) : F) = algebraMap L F (algebraMap A L a)) ∧
      (∀ a : A, χ (φT (Polynomial.C a)) = IsLocalRing.residue A a) ∧
      χ (φT Polynomial.X) = 0 ∧
      (∃ _ : IsLocalRing ↥(SemistableModel.localRing X φ x),
        RingHom.ker χ = IsLocalRing.maximalIdeal ↥(SemistableModel.localRing X φ x) ∧
        IsLocalRing.maximalIdeal ↥(SemistableModel.localRing X φ x) = Ideal.span {φT (Polynomial.C ϖ), φT Polynomial.X}) ∧
      Function.Surjective χ ∧
      φT.FormallySmooth ∧ φT.FormallyUnramified ∧ φT.EssFiniteType ∧
      φT Polynomial.X ∉ Ideal.span {φT (Polynomial.C ϖ)} ∧
      (∀ f : F, ∃ g h : ↥(SemistableModel.localRing X φ x), (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) := by
  classical

  obtain ⟨hdom, hcs, hcf, hsurj, t, hm, ht⟩ :=
    AlgebraicCurve.SemistableModel.exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing
      ϖ hϖ X toBase φ hφ x hx hxc hxs
  set c : A →+* X.presheaf.stalk x :=
    (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) with hc
  haveI := hdom
  obtain ⟨hψs, hψu, hψf⟩ :=
    RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair ϖ hϖ c hcs hcf hsurj t hm ht
  set ψ := Polynomial.eval₂RingHom c t with hψ

  let O := X.presheaf.stalk x
  let θ : ↑O →+* F := φ.symm.toRingHom.comp (algebraMap O X.functionField)
  let θR : ↑O →+* ↥(SemistableModel.localRing X φ x) :=
    { toFun := fun s => ⟨θ s, ⟨s, rfl⟩⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun a b => Subtype.ext (map_mul θ a b)
      map_zero' := Subtype.ext (map_zero θ)
      map_add' := fun a b => Subtype.ext (map_add θ a b) }
  have hθRv : ∀ s, ((θR s : ↥(SemistableModel.localRing X φ x)) : F) = φ.symm (algebraMap O X.functionField s) := fun s => rfl
  have hθRinj : Function.Injective θR := fun a b h => by
    have : θ a = θ b := congrArg (fun z : ↥(SemistableModel.localRing X φ x) => (z : F)) h
    exact (φ.symm.injective.comp (IsFractionRing.injective O X.functionField)) this
  have hθRsurj : Function.Surjective θR := fun q => by
    obtain ⟨s, hs⟩ := q.2
    exact ⟨s, Subtype.ext hs⟩
  let e : ↑O ≃+* ↥(SemistableModel.localRing X φ x) := RingEquiv.ofBijective θR ⟨hθRinj, hθRsurj⟩
  have he : ∀ s, e s = θR s := fun s => rfl
  haveI hloc : IsLocalRing ↥(SemistableModel.localRing X φ x) := IsLocalRing.of_surjective' θR hθRsurj

  have hθc : ∀ a : A, θ (c a) = algebraMap L F (algebraMap A L a) := by
    intro a
    show φ.symm (algebraMap O X.functionField (c a)) = _
    have h1 : algebraMap O X.functionField (c a) = SemistableModel.baseToFunctionField toBase a := by
      show (X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes _).hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [h1, ← hφ, RingEquiv.symm_apply_apply]

  have hcϖ : c ϖ ∈ maximalIdeal O := by rw [hm]; exact Ideal.subset_span (by simp)
  have hker : ∀ a ∈ maximalIdeal A, ((IsLocalRing.residue O).comp c) a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    show IsLocalRing.residue O (c (ϖ * b)) = 0
    rw [map_mul, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ hcϖ
  let ι : ResidueField A →+* ResidueField O := Ideal.Quotient.lift (maximalIdeal A) ((IsLocalRing.residue O).comp c) hker
  have hι : ∀ a : A, ι (IsLocalRing.residue A a) = IsLocalRing.residue O (c a) := fun a => rfl
  have hιbij : Function.Bijective ι := by
    refine ⟨ι.injective, fun r => ?_⟩
    obtain ⟨a, ha⟩ := hsurj r
    exact ⟨IsLocalRing.residue A a, by rw [hι]; exact ha⟩
  let ιe : ResidueField A ≃+* ResidueField O := RingEquiv.ofBijective ι hιbij

  let φT : Polynomial A →+* ↥(SemistableModel.localRing X φ x) := e.toRingHom.comp ψ
  let χ : ↥(SemistableModel.localRing X φ x) →+* ResidueField A :=
    ιe.symm.toRingHom.comp ((IsLocalRing.residue O).comp e.symm.toRingHom)
  have hφTC : ∀ a : A, φT (Polynomial.C a) = e (c a) := by
    intro a; show e (ψ (Polynomial.C a)) = e (c a); rw [hψ]; simp [Polynomial.eval₂RingHom]
  have hφTX : φT Polynomial.X = e t := by
    show e (ψ Polynomial.X) = e t; rw [hψ]; simp [Polynomial.eval₂RingHom]
  have hχe : ∀ s : O, χ (e s) = ιe.symm (IsLocalRing.residue O s) := by
    intro s; show ιe.symm (IsLocalRing.residue O (e.symm (e s))) = _; rw [RingEquiv.symm_apply_apply]

  have hmaxS : maximalIdeal ↥(SemistableModel.localRing X φ x) = (maximalIdeal O).map e.toRingHom := by
    apply le_antisymm
    · intro q hq
      obtain ⟨s, rfl⟩ := hθRsurj q
      rw [← he]
      refine Ideal.mem_map_of_mem _ ?_
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hq ⊢
      exact fun hu => hq (by rw [← he]; exact hu.map e)
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
      intro hu
      apply hs
      have := hu.map e.symm
      simpa using this
  refine ⟨φT, χ, ?hAS, ?hφC, ?hχC, ?hχt, ⟨hloc, ?hkerχ, ?hmax⟩, ?hχsurj, ?hs, ?hu, ?hf, ?hnot, ?hfrac⟩
  case hAS =>
    intro a
    rw [← hθc]
    exact ⟨c a, rfl⟩
  case hφC =>
    intro a
    rw [hφTC, he, hθRv]
    exact hθc a
  case hχC =>
    intro a
    rw [hφTC, hχe, ← hι]
    show ιe.symm (ιe (IsLocalRing.residue A a)) = _
    rw [RingEquiv.symm_apply_apply]
  case hχt =>
    rw [hφTX, hχe, (IsLocalRing.residue_eq_zero_iff _).mpr (by rw [hm]; exact Ideal.subset_span (by simp)), map_zero]
  case hkerχ =>
    rw [hmaxS]
    ext q
    obtain ⟨s, rfl⟩ := hθRsurj q
    rw [RingHom.mem_ker, ← he, hχe, map_eq_zero_iff _ ιe.symm.injective, IsLocalRing.residue_eq_zero_iff]
    constructor
    · intro h; exact Ideal.mem_map_of_mem _ h
    · intro h
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at h
      obtain ⟨s', hs', hss'⟩ := h
      have : s' = s := e.injective hss'
      rw [← this]; exact hs'
  case hmax =>
    rw [hmaxS, hm, Ideal.map_span, hφTC, hφTX]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨_, Or.inl rfl, rfl⟩
      · exact ⟨_, Or.inr rfl, rfl⟩
  case hχsurj =>
    intro k
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (R := O) (ιe k)
    refine ⟨e s, ?_⟩
    rw [hχe, hs, RingEquiv.symm_apply_apply]
  case hs => exact RingHom.FormallySmooth.respectsIso.1 ψ e hψs
  case hu => exact RingHom.FormallyUnramified.respectsIso.1 ψ e hψu
  case hf => exact RingHom.EssFiniteType.respectsIso.1 ψ e hψf
  case hnot =>
    rw [hφTX, hφTC]
    intro hmem
    apply ht
    rw [Ideal.mem_span_singleton] at hmem ⊢
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨s, rfl⟩ := hθRsurj q
    rw [← he, ← map_mul] at hq
    exact ⟨s, e.injective hq⟩
  case hfrac =>
    intro f
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (φ f)
    refine ⟨θR a, θR b, ?_, ?_⟩
    · rw [hθRv]
      intro h0
      have : algebraMap O X.functionField (b : O) = 0 := by
        have := congrArg φ h0; rwa [RingEquiv.apply_symm_apply, map_zero] at this
      exact nonZeroDivisors.ne_zero b.2 ((IsFractionRing.injective O X.functionField) (by rw [this, map_zero]))
    · rw [hθRv, hθRv]
      apply φ.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hab

end S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing (solution)
