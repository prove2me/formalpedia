-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fb7687d0-7b65-5123-8f5c-c14a827490f5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

open CategoryTheory.Limits in
theorem solution
    {R : Type u} [CommRing R] {Z Y : Scheme.{u}}
    (fZ : Z ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))

    (η : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z),
      z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)) → (Spec (CommRingCat.of C) ⟶ Y))

    (hη_over : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
      (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))),
      η C z hz ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap R C)))

    (hη_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C'] (φ : C →ₐ[R] C')
      (z : Spec (CommRingCat.of C) ⟶ Z) (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (hz' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C'))),
      η C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) hz' = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ η C z hz) :
    ∃ u : Z ⟶ Y, u ≫ fY = fZ ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
        (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ u = η C z hz) ∧
      ∀ v : Z ⟶ Y,
        (∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
          (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ v = η C z hz) → v = u := by
  classical

  have ηcongr : ∀ (C : Type u) [CommRing C] [Algebra R C] (z₁ z₂ : Spec (CommRingCat.of C) ⟶ Z)
      (h₁ : z₁ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (h₂ : z₂ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z₁ = z₂ → η C z₁ h₁ = η C z₂ h₂ := by
    intro C _ _ z₁ z₂ h₁ h₂ e; subst e; rfl

  have nat' : ∀ (C C' : Type u) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (ψ : C →+* C')
      (hψ : ψ.comp (algebraMap R C) = algebraMap R C')
      (z : Spec (CommRingCat.of C) ⟶ Z) (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (hz' : (Spec.map (CommRingCat.ofHom ψ) ≫ z) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C'))),
      η C' (Spec.map (CommRingCat.ofHom ψ) ≫ z) hz' = Spec.map (CommRingCat.ofHom ψ) ≫ η C z hz := by
    intro C C' _ _ _ _ ψ hψ z hz hz'
    exact hη_nat C C' ⟨ψ, fun r => DFunLike.congr_fun hψ r⟩ z hz hz'

  have compat : ∀ (C C' : Type u) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (ψ : C →+* C'),
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
        Spec.map (CommRingCat.ofHom (algebraMap R C')) →
      ψ.comp (algebraMap R C) = algebraMap R C' := by
    intro C C' _ _ _ _ ψ h
    rw [← Spec.map_comp, Spec.map_inj] at h
    ext r
    have h' := congrArg (fun χ => CommRingCat.Hom.hom χ r) h
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using h'

  have mkAlg : ∀ (S : CommRingCat.{u}) (w : Spec S ⟶ Z),
      ∃ inst : Algebra R S, w ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap (R := R) (A := S))) := by
    intro S w
    refine ⟨(Spec.preimage (w ≫ fZ)).hom.toAlgebra, ?_⟩
    change w ≫ fZ = Spec.map (CommRingCat.ofHom (Spec.preimage (w ≫ fZ)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]

  have over_comp : ∀ (C C' : Type u) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (ψ : C →+* C')
      (hψ : ψ.comp (algebraMap R C) = algebraMap R C')
      (z : Spec (CommRingCat.of C) ⟶ Z) (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))),
      (Spec.map (CommRingCat.ofHom ψ) ≫ z) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C')) := by
    intro C C' _ _ _ _ ψ hψ z hz
    rw [Category.assoc, hz, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]

  let 𝒰 := Z.affineOpenCover
  let inst : ∀ i, Algebra R (𝒰.X i) := fun i => (mkAlg (𝒰.X i) (𝒰.f i)).choose
  have hzI : ∀ i, 𝒰.f i ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap (R := R) (A := 𝒰.X i))) :=
    fun i => (mkAlg (𝒰.X i) (𝒰.f i)).choose_spec
  let g : ∀ i, Spec (𝒰.X i) ⟶ Y := fun i => η (𝒰.X i) (𝒰.f i) (hzI i)

  have key : ∀ (i : 𝒰.I₀) (D : Type u) [CommRing D] [Algebra R D] (w : Spec (CommRingCat.of D) ⟶ Spec (𝒰.X i))
      (hw : (w ≫ 𝒰.f i) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R D))),
      w ≫ g i = η D (w ≫ 𝒰.f i) hw := by
    intro i D _ _ w hw
    let ψ : 𝒰.X i ⟶ CommRingCat.of D := Spec.preimage w
    have hψw : Spec.map ψ = w := Spec.map_preimage w
    have hψ : ψ.hom.comp (algebraMap R (𝒰.X i)) = algebraMap R D := by
      apply compat
      rw [← hzI i, CommRingCat.ofHom_hom, hψw, ← Category.assoc, hw]
    have hw' : (Spec.map (CommRingCat.ofHom ψ.hom) ≫ 𝒰.f i) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [CommRingCat.ofHom_hom, hψw]; exact hw
    have hnat := nat' (𝒰.X i) D ψ.hom hψ (𝒰.f i) (hzI i) hw'
    have e : Spec.map (CommRingCat.ofHom ψ.hom) = w := by rw [CommRingCat.ofHom_hom, hψw]
    calc w ≫ g i = Spec.map (CommRingCat.ofHom ψ.hom) ≫ g i := by rw [e]
      _ = η D (Spec.map (CommRingCat.ofHom ψ.hom) ≫ 𝒰.f i) hw' := hnat.symm
      _ = η D (w ≫ 𝒰.f i) hw := ηcongr D _ _ hw' hw (by rw [e])

  have hcompat : ∀ i j : 𝒰.I₀,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    let 𝒱 := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover
    refine 𝒱.openCover.hom_ext _ _ fun k => ?_
    change 𝒱.f k ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = 𝒱.f k ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j
    obtain ⟨instk, hk⟩ := mkAlg (𝒱.X k) ((𝒱.f k ≫ pullback.fst (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f i)
    letI := instk
    have hk' : ((𝒱.f k ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j) ≫ fZ =
        Spec.map (CommRingCat.ofHom (algebraMap R (𝒱.X k))) := by
      rw [← hk]; simp only [Category.assoc, pullback.condition_assoc]
    rw [← Category.assoc, ← Category.assoc, @key i (𝒱.X k) _ instk _ hk, @key j (𝒱.X k) _ instk _ hk']
    apply @ηcongr (𝒱.X k) _ instk
    rw [Category.assoc, Category.assoc, pullback.condition]
  let u : Z ⟶ Y := 𝒰.openCover.glueMorphisms g hcompat
  have hu : ∀ i, 𝒰.f i ≫ u = g i := fun i => 𝒰.openCover.ι_glueMorphisms g hcompat i

  have hpt : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
      (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ u = η C z hz := by
    intro C _ _ z hz

    have loc : ∀ p : PrimeSpectrum C, ∃ (c : C) (i : 𝒰.I₀), c ∉ p.asIdeal ∧
        ∀ q : PrimeSpectrum C, c ∉ q.asIdeal → z.base q ∈ Set.range (𝒰.f i).base := by
      intro p
      obtain ⟨i, y, hy⟩ := 𝒰.openCover.exists_eq (z.base p)
      have hO : IsOpen (z.base ⁻¹' Set.range (𝒰.f i).base) :=
        (𝒰.f i).isOpenEmbedding.isOpen_range.preimage z.continuous
      have hpO : p ∈ z.base ⁻¹' Set.range (𝒰.f i).base := ⟨y, hy⟩
      obtain ⟨_, ⟨c, rfl⟩, hpc, hcO⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpO hO
      exact ⟨c, i, hpc, fun q hq => hcO hq⟩
    choose c idx hc hrange using loc
    have hspan : Ideal.span (Set.range c) = ⊤ := by
      by_contra h
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
      exact hc ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))
    let 𝒲 := Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) c hspan
    refine 𝒲.openCover.hom_ext _ _ fun p => ?_
    change Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (c p)))) ≫ z ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (c p)))) ≫ η C z hz
    let A : Type u := Localization.Away (c p)
    let zp : Spec (CommRingCat.of A) ⟶ Z := Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ z
    have hzp_range : Set.range zp.base ⊆ Set.range (𝒰.f (idx p)).base := by
      rintro _ ⟨r, rfl⟩
      change z.base ((Spec.map (CommRingCat.ofHom (algebraMap C A))).base r) ∈ _
      apply hrange p
      change algebraMap C A (c p) ∉ r.asIdeal
      exact fun hmem => r.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
        (IsLocalization.Away.algebraMap_isUnit (c p)))
    let w : Spec (CommRingCat.of A) ⟶ Spec (𝒰.X (idx p)) := IsOpenImmersion.lift (𝒰.f (idx p)) zp hzp_range
    have hw : w ≫ 𝒰.f (idx p) = zp := IsOpenImmersion.lift_fac _ _ _
    have halg : (algebraMap C A).comp (algebraMap R C) = algebraMap R A :=
      (IsScalarTower.algebraMap_eq R C A).symm
    have hzp : zp ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R A)) := over_comp C A _ halg z hz
    have hwz : (w ≫ 𝒰.f (idx p)) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by rw [hw]; exact hzp
    calc Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ z ≫ u
        = w ≫ 𝒰.f (idx p) ≫ u := by rw [← Category.assoc]; change zp ≫ u = _; rw [← hw, Category.assoc]
      _ = w ≫ g (idx p) := by rw [hu]
      _ = η A (w ≫ 𝒰.f (idx p)) hwz := key (idx p) A w hwz
      _ = η A zp hzp := ηcongr A _ _ hwz hzp hw
      _ = Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ η C z hz := nat' C A (algebraMap C A) halg z hz hzp

  refine ⟨u, ?_, hpt, ?_⟩
  · refine 𝒰.openCover.hom_ext _ _ fun i => ?_
    change 𝒰.f i ≫ u ≫ fY = 𝒰.f i ≫ fZ
    rw [← Category.assoc, hu i, hzI i]
    exact @hη_over (𝒰.X i) _ (inst i) (𝒰.f i) (hzI i)
  · intro v hv
    refine 𝒰.openCover.hom_ext _ _ fun i => ?_
    change 𝒰.f i ≫ v = 𝒰.f i ≫ u
    rw [@hv (𝒰.X i) _ (inst i) (𝒰.f i) (hzI i), hu i]

end S_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural (solution)
