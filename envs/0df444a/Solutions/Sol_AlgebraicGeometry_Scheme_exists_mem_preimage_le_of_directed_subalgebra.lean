-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_mem_preimage_le_of_directed_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/60ae9b0e-7564-5f66-a20f-e3d915b1c15e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

open scoped TensorProduct

namespace ProBasisGC4

section Chart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (C : CommRingCat.{u}) (uC : Spec C ⟶ X) [IsOpenImmersion uC]

@[reducible] noncomputable def chartAlgebra : Algebra R C := (Spec.preimage (uC ≫ f)).hom.toAlgebra

theorem comp_eq_SpecMap :
    letI := chartAlgebra f C uC
    uC ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  letI := chartAlgebra f C uC
  have : CommRingCat.ofHom (algebraMap R C) = Spec.preimage (uC ≫ f) := rfl
  rw [this, Spec.map_preimage]

variable (T : Type u) [CommRing T] [Algebra R T]

noncomputable def chartMap :
    letI := chartAlgebra f C uC
    Spec (CommRingCat.of (C ⊗[R] T)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
  letI := chartAlgebra f C uC
  (pullbackSpecIso R C T).inv ≫ (pullback.congrHom (comp_eq_SpecMap f C uC) rfl).inv ≫
    pullback.map (uC ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R T))) f
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) uC (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem chartMap_fst :
    letI := chartAlgebra f C uC
    chartMap f C uC T ≫ pullback.fst f _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := C) (B := T))) ≫ uC := by
  letI := chartAlgebra f C uC
  simp only [chartMap, Category.assoc, pullback.lift_fst, pullback.congrHom_inv, pullback.lift_fst_assoc,
    Category.comp_id]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]

theorem chartMap_snd :
    letI := chartAlgebra f C uC
    chartMap f C uC T ≫ pullback.snd f _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := T)).toRingHom) := by
  letI := chartAlgebra f C uC
  simp only [chartMap, Category.assoc, pullback.lift_snd, pullback.congrHom_inv,
    Category.comp_id]
  exact pullbackSpecIso_inv_snd R C T

scoped instance chartMap_isOpenImmersion :
    letI := chartAlgebra f C uC
    IsOpenImmersion (chartMap f C uC T) := by
  letI := chartAlgebra f C uC
  unfold chartMap
  infer_instance

theorem mem_range_chartMap (p : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R T)))))
    (hp : pullback.fst f _ p ∈ Set.range uC) :
    letI := chartAlgebra f C uC
    p ∈ Set.range (chartMap f C uC T) := by
  letI := chartAlgebra f C uC
  have h1 : p ∈ Set.range (pullback.map (uC ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R T))) f
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) uC (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
    rw [Scheme.Pullback.range_map]
    exact ⟨hp, by simp⟩
  obtain ⟨p₁, rfl⟩ := h1
  refine ⟨(pullbackSpecIso R C T).hom ((pullback.congrHom (comp_eq_SpecMap f C uC) rfl).hom p₁), ?_⟩
  change ((pullback.congrHom (comp_eq_SpecMap f C uC) rfl).hom ≫ (pullbackSpecIso R C T).hom ≫
    chartMap f C uC T) p₁ = _
  simp only [chartMap, Iso.hom_inv_id_assoc]

end Chart

section Transition

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (C : CommRingCat.{u}) (uC : Spec C ⟶ X) [IsOpenImmersion uC]

noncomputable def τ : letI := chartAlgebra f C uC; C ⊗[R] ↥S →ₐ[R] C ⊗[R] A :=
  letI := chartAlgebra f C uC
  Algebra.TensorProduct.map (AlgHom.id R C) S.val

theorem chartMap_comp_q
    (q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S))))
    (hq₁ : q ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S A))) :
    letI := chartAlgebra f C uC
    chartMap f C uC A ≫ q = Spec.map (CommRingCat.ofHom (τ S f C uC).toRingHom) ≫ chartMap f C uC ↥S := by
  letI := chartAlgebra f C uC
  have e1 : (τ S f C uC).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := C) (B := ↥S)) =
      Algebra.TensorProduct.includeLeftRingHom := RingHom.ext fun c => by
    change (τ S f C uC) (c ⊗ₜ 1) = c ⊗ₜ 1
    simp [τ]
  have e2 : (τ S f C uC).toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := ↥S)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := A)).toRingHom.comp (algebraMap ↥S A) :=
    RingHom.ext fun s => by
      change (τ S f C uC) (1 ⊗ₜ s) = (1 : C) ⊗ₜ[R] (algebraMap ↥S A s)
      simp [τ]
  apply pullback.hom_ext
  · rw [Category.assoc, hq₁, chartMap_fst, Category.assoc, chartMap_fst, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, e1]
  · rw [Category.assoc, hq₂, ← Category.assoc, chartMap_snd, Category.assoc, chartMap_snd, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e2]

end Transition

theorem mem_preimage_basicOpen {T T' : Type u} [CommRing T] [CommRing T'] (φ : T →+* T') (t : T)
    (x : ↥(Spec (CommRingCat.of T'))) :
    (Spec.map (CommRingCat.ofHom φ)) x ∈ (PrimeSpectrum.basicOpen t : (Spec (CommRingCat.of T)).Opens) ↔
      x ∈ (PrimeSpectrum.basicOpen (φ t) : (Spec (CommRingCat.of T')).Opens) :=
  Iff.rfl

end ProBasisGC4
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.ProBasisGC4"

open ProBasisGC4 in
theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type v} (S : ι → Subalgebra R A) (hdir : Directed (· ≤ ·) S) (hS : ∀ a : A, ∃ i, a ∈ S i)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (q : ∀ i, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i)))))
    (hq₁ : ∀ i, q i ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : ∀ i, q i ≫ pullback.snd f _ =
      pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(S i) A)))
    (U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Opens)
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))))) (hw : w ∈ U) :
    ∃ (i : ι) (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i))))).Opens),
      w ∈ (q i) ⁻¹ᵁ W ∧ (q i) ⁻¹ᵁ W ≤ U := by
  classical
  haveI : Nonempty ι := by obtain ⟨i, -⟩ := hS 0; exact ⟨i⟩

  let 𝒰 := X.affineOpenCover
  let k := 𝒰.idx (pullback.fst f _ w)
  let C : CommRingCat := 𝒰.X k
  let uC : Spec C ⟶ X := 𝒰.f k
  haveI : IsOpenImmersion uC := 𝒰.map_prop k
  letI := chartAlgebra f C uC
  obtain ⟨w₀, hw₀⟩ := mem_range_chartMap f C uC A w (𝒰.covers _)

  have hw₀U : w₀ ∈ (chartMap f C uC A) ⁻¹ᵁ U := by
    change (chartMap f C uC A) w₀ ∈ U; rw [hw₀]; exact hw
  obtain ⟨_, ⟨s, rfl⟩, hws, hsU⟩ :=
    (Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := C ⊗[R] A))) hw₀U

  obtain ⟨F, hF⟩ := TensorProduct.exists_finset s
  choose j hj using hS
  obtain ⟨i, hi⟩ := hdir.finset_le (F.image fun p => j p.2)
  have hmem : ∀ p ∈ F, p.2 ∈ S i := fun p hp => hi _ (Finset.mem_image_of_mem _ hp) (hj p.2)
  let s' : C ⊗[R] ↥(S i) := ∑ p ∈ F.attach, p.1.1 ⊗ₜ (⟨p.1.2, hmem p.1 p.2⟩ : ↥(S i))
  have hs' : (τ (S i) f C uC) s' = s := by
    rw [hF, map_sum, ← Finset.sum_attach F]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [τ]

  refine ⟨i, (chartMap f C uC ↥(S i)) ''ᵁ (PrimeSpectrum.basicOpen s'), ?_, ?_⟩
  ·
    change (q i) w ∈ (chartMap f C uC ↥(S i)) ''ᵁ (PrimeSpectrum.basicOpen s')
    rw [← hw₀, ← Scheme.Hom.comp_apply, chartMap_comp_q (S i) f C uC (q i) (hq₁ i) (hq₂ i), Scheme.Hom.comp_apply]
    refine ⟨(Spec.map (CommRingCat.ofHom (τ (S i) f C uC).toRingHom)) w₀, ?_, rfl⟩
    rw [SetLike.mem_coe]
    refine (mem_preimage_basicOpen (τ (S i) f C uC).toRingHom s' w₀).mpr ?_
    change w₀ ∈ PrimeSpectrum.basicOpen ((τ (S i) f C uC) s')
    rw [hs']; exact hws
  ·
    intro p hp
    change (q i) p ∈ (chartMap f C uC ↥(S i)) ''ᵁ (PrimeSpectrum.basicOpen s') at hp
    rw [← SetLike.mem_coe, Scheme.Hom.coe_image] at hp
    obtain ⟨y, hy, hyp⟩ := hp

    have hpfst : pullback.fst f _ p ∈ Set.range uC := by
      rw [← hq₁ i, Scheme.Hom.comp_apply, ← hyp, ← Scheme.Hom.comp_apply, chartMap_fst, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    obtain ⟨p₀, rfl⟩ := mem_range_chartMap f C uC A p hpfst

    have hq' : (chartMap f C uC ↥(S i)) ((Spec.map (CommRingCat.ofHom (τ (S i) f C uC).toRingHom)) p₀) =
        (chartMap f C uC ↥(S i)) y := by
      rw [hyp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, chartMap_comp_q (S i) f C uC (q i) (hq₁ i) (hq₂ i)]
    have hy' := (chartMap f C uC ↥(S i)).isOpenEmbedding.injective hq'
    have hp₀ : p₀ ∈ (PrimeSpectrum.basicOpen s : (Spec (CommRingCat.of (C ⊗[R] A))).Opens) := by
      rw [← hs']
      exact (mem_preimage_basicOpen (τ (S i) f C uC).toRingHom s' p₀).mp (by rw [hy']; exact hy)
    exact hsU hp₀

end S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra (solution)
