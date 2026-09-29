-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.fibre_shapes_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/15afd25a-d2fc-5f86-ada1-f04c7ef34d24

import Theorems.Thm_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_fibre_shapes_of_level

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

namespace T4bSol

section Core
variable {L : Type u} [Field L] {A : ValuationSubring L} {F : Type u'} [Field F] [Algebra L F]
  {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
  {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
  {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))} {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
  (M : SemistableModel A F Fbar C An src tgt xs xt)

theorem pt_ne_genericPoint (P : Place L F) : M.pt P ≠ genericPoint M.X := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inl P)) (Sum.inl ()) h
  simp at this

theorem gen_ne_genericPoint (i : ιV) : M.gen i ≠ genericPoint M.X := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inl ()) h
  simp at this

theorem sm_ne_genericPoint (i : ιV) (q : {Q : Place (IsLocalRing.ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) :
    M.sm i q ≠ genericPoint M.X := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, q⟩)))) (Sum.inl ()) h
  simp at this

theorem nd_ne_genericPoint (e₁ : ιE) : M.nd e₁ ≠ genericPoint M.X := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inr (Sum.inr (Sum.inr e₁)))) (Sum.inl ()) h
  simp at this

theorem pt_ne_gen (P : Place L F) (i : ιV) : M.pt P ≠ M.gen i := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inl P)) (Sum.inr (Sum.inr (Sum.inl i))) h
  simp at this

theorem pt_ne_nd (P : Place L F) (e₁ : ιE) : M.pt P ≠ M.nd e₁ := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inl P)) (Sum.inr (Sum.inr (Sum.inr (Sum.inr e₁)))) h
  simp at this

theorem pt_ne_sm (P : Place L F) (i : ιV) (q : {Q : Place (IsLocalRing.ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) :
    M.pt P ≠ M.sm i q := fun h => by
  have := @M.classify_bijective.1 (Sum.inr (Sum.inl P)) (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, q⟩)))) h
  simp at this

theorem mem_of_isIntegral_subfield (K : Subfield F) (V : ValuationSubring F) (hKV : ∀ x : K, (x : F) ∈ V) (y : F)
    (hy : IsIntegral K y) : y ∈ V := by
  have hV : V.valuation.Integers V :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun a => V.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, (V.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  rw [← V.valuation_le_one_iff, ← hV.isIntegral_iff_v_le_one]
  obtain ⟨p, hp, hpy⟩ := hy
  let j : K →+* V :=
    { toFun := fun x => ⟨x, hKV x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  refine ⟨p.map j, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  convert hpy using 2
  rfl
  rfl

theorem toBase_eq_closedPoint_of_gen_specializes (i : ιV) (x : M.X) (h : M.gen i ⤳ x) :
    M.toBase.base x = IsLocalRing.closedPoint A := by
  have h' : M.toBase.base (M.gen i) ⤳ M.toBase.base x := h.map M.toBase.base.hom.continuous
  rw [M.toBase_gen] at h'
  have hle := (PrimeSpectrum.le_iff_specializes _ _).mpr h'
  exact (PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (M.toBase.base x).2.ne_top hle)).symm

theorem base_asIdeal_eq_comap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    (f.base x).asIdeal = Ideal.comap ((X.presheaf.Γgerm x).hom.comp (f.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  have hfac : f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  conv_lhs => rw [hfac]
  rfl

end Core

end T4bSol

open T4bSol in
set_option linter.unusedVariables false in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : ↥A, y ∈ IsLocalRing.maximalIdeal ↥A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (A₁ : Type u) [CommRing A₁] [IsLocalRing A₁] (hA₁ : ∃ t : A₁, t ≠ 0 ∧ t ∈ IsLocalRing.maximalIdeal A₁)
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁)
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField) (halg : Algebra.IsAlgebraic F₁ F)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s))) :
    (∀ x x' : M.X, (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x' =
        (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x →
      M.toBase.base x = IsLocalRing.closedPoint ↥A → x' = x) ∧
    (∀ x' : M.X, (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x' =
        (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) →
      x' = genericPoint M.X) ∧
    (∀ (P : Place L F) (x' : M.X), (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x' =
        (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P) →
      ∃ P' : Place L F, x' = M.pt P') ∧
    (IsClosedMap (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base →
      _root_.IsPreconnected (f₁.base ⁻¹' {IsLocalRing.closedPoint A₁}) →
      _root_.IsPreconnected (M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A})) := by
  classical
  obtain ⟨hgen, hcompat⟩ := hcompat
  set π : M.X ⟶ X₁ := e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) with hπdef
  let Sι := Spec.map (CommRingCat.ofHom ι₁)

  have hsq : π ≫ f₁ = M.toBase ≫ Sι := by
    rw [hπdef, Category.assoc, pullback.condition, ← Category.assoc, he₁]
  have hbase : ∀ x : M.X, f₁.base (π.base x) = Sι.base (M.toBase.base x) := by
    intro x
    have := congrArg (fun φ => φ.base x) hsq
    simpa using this

  obtain ⟨t, ht0, htm⟩ := hA₁
  let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hSs : Sι.base (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint A₁ :=
    IsLocalRing.comap_closedPoint ι₁
  have hSη : Sι.base η ≠ IsLocalRing.closedPoint A₁ := by
    intro h
    have h1 : (PrimeSpectrum.comap ι₁ η).asIdeal = ⊥ := by
      show Ideal.comap ι₁ ⊥ = ⊥
      exact Ideal.comap_bot_of_injective ι₁ hι₁
    have h2 : PrimeSpectrum.comap ι₁ η = IsLocalRing.closedPoint A₁ := h
    rw [h2] at h1
    have htm' : t ∈ (IsLocalRing.closedPoint A₁).asIdeal := htm
    rw [h1] at htm'
    exact ht0 (Ideal.mem_bot.mp htm')
  have hηs : η ≠ IsLocalRing.closedPoint A := fun h => hSη (h ▸ hSs)

  have hξ : M.toBase.base (genericPoint M.X) = η := by
    apply PrimeSpectrum.ext
    rw [base_asIdeal_eq_comap]
    show Ideal.comap _ (IsLocalRing.maximalIdeal M.X.functionField) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    refine (RingHom.injective_iff_ker_eq_bot _).mp ?_
    intro a b hab
    have ha := M.ffEquiv_algebraMap a
    have hb := M.ffEquiv_algebraMap b
    have : M.ffEquiv (algebraMap L F (a : L)) = M.ffEquiv (algebraMap L F (b : L)) := by
      rw [ha, hb]; exact hab
    exact Subtype.ext ((algebraMap L F).injective (M.ffEquiv.injective this))

  have hdich : ∀ x : M.X, M.toBase.base x = IsLocalRing.closedPoint A ∨ M.toBase.base x = η := by
    intro x
    obtain ⟨y, rfl⟩ := M.classify_bijective.2 x
    rcases y with ⟨⟩ | P | i | ⟨i, q⟩ | e₀
    · exact Or.inr hξ
    · exact Or.inr (PrimeSpectrum.ext (M.toBase_pt P))
    · exact Or.inl (M.toBase_gen i)
    · exact Or.inl (toBase_eq_closedPoint_of_gen_specializes M i _ (M.gen_specializes_sm i q))
    · exact Or.inl (toBase_eq_closedPoint_of_gen_specializes M (src e₀) _ (M.gen_specializes_nd e₀).1)

  have hboth : ∀ x x' : M.X, π.base x' = π.base x → M.toBase.base x = IsLocalRing.closedPoint A →
      M.toBase.base x' = IsLocalRing.closedPoint A := by
    intro x x' h hx
    rcases hdich x' with h' | h'
    · exact h'
    · exfalso
      have := hbase x'
      rw [h, hbase x, hx, hSs, h'] at this
      exact hSη this.symm

  let sA := Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))
  let s₁ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))
  obtain ⟨ρ, hρ⟩ := AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback ι₁ hres₁ M.toBase f₁ e₁ he₁
  haveI : IsClosedImmersion s₁ :=
    IsClosedImmersion.spec_of_surjective _ (by simpa using IsLocalRing.residue_surjective)
  have hj₁inj : Function.Injective (pullback.fst f₁ s₁).base :=
    (pullback.fst f₁ s₁).isClosedEmbedding.injective

  have hsA : ∀ p : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)), sA.base p = IsLocalRing.closedPoint ↥A := by
    intro p
    apply PrimeSpectrum.ext
    show Ideal.comap (IsLocalRing.residue ↥A) p.asIdeal = IsLocalRing.maximalIdeal ↥A
    have hp : p.asIdeal = ⊥ := by
      haveI := p.2
      exact (Ideal.eq_bot_of_prime p.asIdeal)
    rw [hp, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  have hlift : ∀ x : M.X, M.toBase.base x = IsLocalRing.closedPoint ↥A →
      ∃ z, (pullback.fst M.toBase sA).base z = x := by
    intro x hx
    let p : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) := IsLocalRing.closedPoint _
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := M.toBase) (g := sA) x p (by rw [hx, hsA])
    exact ⟨z, hz⟩
  have hρfst : ∀ z, (pullback.fst f₁ s₁).base (ρ.hom.base z) = π.base ((pullback.fst M.toBase sA).base z) := by
    intro z
    have := congrArg (fun φ => φ.base z) hρ
    simp at this
    exact this

  have h1 : ∀ x x' : M.X, π.base x' = π.base x → M.toBase.base x = IsLocalRing.closedPoint ↥A → x' = x := by
    intro x x' h hx
    have hx' := hboth x x' h hx
    obtain ⟨z, rfl⟩ := hlift x hx
    obtain ⟨z', rfl⟩ := hlift x' hx'
    have hw : ρ.hom.base z' = ρ.hom.base z := by
      apply hj₁inj
      rw [hρfst, hρfst]
      exact h
    have hinv : ∀ w, ρ.inv.base (ρ.hom.base w) = w := fun w => by
      show (ρ.hom ≫ ρ.inv).base w = w
      rw [Iso.hom_inv_id]; rfl
    have hz : z' = z := by
      have := congrArg (fun w => ρ.inv.base w) hw
      simpa [hinv] using this
    rw [hz]

  have hpt_gen : ∀ P : Place L F, π.base (M.pt P) ≠ π.base (genericPoint M.X) := by
    intro P h

    have hF₁ : ∀ s : F₁, (s : F) ∈ P.toValuationSubring := by
      intro s
      have hloc : (s : F) ∈ SemistableModel.localRing M.X M.ffEquiv (M.pt P) := by
        have hsp : π.base (M.pt P) ⤳ genericPoint X₁ := specializes_of_eq (h.trans hgen)
        set y0 := (X₁.presheaf.stalkSpecializes hsp).hom (φ₁ s) with hy0
        have h12 : genericPoint M.X ⤳ M.pt P := (genericPoint_spec M.X).specializes trivial
        refine ⟨(π.stalkMap (M.pt P)).hom y0, ?_⟩
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra]
        rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, hcompat s]
        have key := congrArg (fun k => (CommRingCat.Hom.hom k) y0)
          (Scheme.Hom.stalkSpecializes_stalkMap π (genericPoint M.X) (M.pt P) h12)
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at key
        change (M.X.presheaf.stalkSpecializes h12).hom ((π.stalkMap (M.pt P)).hom y0) =
          (π.stalkMap (genericPoint M.X)).hom ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s))
        rw [← key, hy0]
        congr 1
        change (X₁.presheaf.stalkSpecializes hsp ≫ X₁.presheaf.stalkSpecializes _).hom (φ₁ s) = _
        rw [TopCat.Presheaf.stalkSpecializes_comp]
      rw [M.localRing_pt] at hloc
      exact hloc

    have hall : ∀ f : F, f ∈ P.toValuationSubring := by
      intro f
      refine mem_of_isIntegral_subfield F₁ P.toValuationSubring (fun s => hF₁ s) f ?_
      exact (isAlgebraic_iff_isIntegral.mp (halg.isAlgebraic f))
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
    have hϖ0 : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
    have hinv := hall (ϖ : F)⁻¹
    apply hϖ.not_isUnit
    exact ⟨⟨ϖ, ⟨(ϖ : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hϖ0), Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩
  have h2 : ∀ x' : M.X, π.base x' = π.base (genericPoint M.X) → x' = genericPoint M.X := by
    intro x' h
    obtain ⟨y, rfl⟩ := M.classify_bijective.2 x'
    rcases y with ⟨⟩ | P | i | ⟨i, q⟩ | e₀
    · rfl
    · exact absurd h (hpt_gen P)
    · exact (h1 _ _ h.symm (M.toBase_gen i)).symm
    · exact (h1 _ _ h.symm (toBase_eq_closedPoint_of_gen_specializes M i _ (M.gen_specializes_sm i q))).symm
    · exact (h1 _ _ h.symm (toBase_eq_closedPoint_of_gen_specializes M (src e₀) _ (M.gen_specializes_nd e₀).1)).symm

  have h3 : ∀ (P : Place L F) (x' : M.X), π.base x' = π.base (M.pt P) → ∃ P' : Place L F, x' = M.pt P' := by
    intro P x' h
    obtain ⟨y, rfl⟩ := M.classify_bijective.2 x'
    rcases y with ⟨⟩ | P' | i | ⟨i, q⟩ | e₀
    · exact absurd h.symm (hpt_gen P)
    · exact ⟨P', rfl⟩
    · exact absurd (h1 _ _ h.symm (M.toBase_gen i)) (pt_ne_gen M P i)
    · exact absurd (h1 _ _ h.symm (toBase_eq_closedPoint_of_gen_specializes M i _ (M.gen_specializes_sm i q)))
        (pt_ne_sm M P i _)
    · exact absurd (h1 _ _ h.symm (toBase_eq_closedPoint_of_gen_specializes M (src e₀) _ (M.gen_specializes_nd e₀).1))
        (pt_ne_nd M P e₀)

  have h4 : IsClosedMap π.base → _root_.IsPreconnected (f₁.base ⁻¹' {IsLocalRing.closedPoint A₁}) →
      _root_.IsPreconnected (M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A}) := by
    intro _ hconn

    have hs₁ : ∀ p : Spec (CommRingCat.of (IsLocalRing.ResidueField A₁)), s₁.base p = IsLocalRing.closedPoint A₁ := by
      intro p
      apply PrimeSpectrum.ext
      show Ideal.comap (IsLocalRing.residue A₁) p.asIdeal = IsLocalRing.maximalIdeal A₁
      have hp : p.asIdeal = ⊥ := by
        haveI := p.2
        exact (Ideal.eq_bot_of_prime p.asIdeal)
      rw [hp, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    have hr₁ : Set.range (pullback.fst f₁ s₁).base = f₁.base ⁻¹' {IsLocalRing.closedPoint A₁} := by
      rw [Scheme.Pullback.range_fst]
      congr 1
      ext q
      simp only [Set.mem_range]
      exact ⟨fun ⟨p, hp⟩ => hp ▸ hs₁ p, fun hq => ⟨IsLocalRing.closedPoint _, (hs₁ _).trans hq.symm⟩⟩
    have hrA : Set.range (pullback.fst M.toBase sA).base = M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A} := by
      rw [Scheme.Pullback.range_fst]
      congr 1
      ext q
      simp only [Set.mem_range]
      exact ⟨fun ⟨p, hp⟩ => hp ▸ hsA p, fun hq => ⟨IsLocalRing.closedPoint _, (hsA _).trans hq.symm⟩⟩

    rw [← hr₁, ← Set.image_univ] at hconn
    have huniv₁ : _root_.IsPreconnected (Set.univ : Set ↥(pullback f₁ s₁)) :=
      ((pullback.fst f₁ s₁).isClosedEmbedding.isInducing.isPreconnected_image).mp hconn
    have hunivA : _root_.IsPreconnected (Set.univ : Set ↥(pullback M.toBase sA)) := by
      have := huniv₁.image ρ.inv.base ρ.inv.base.hom.continuous.continuousOn
      rwa [Set.image_univ_of_surjective] at this
      intro z
      refine ⟨ρ.hom.base z, ?_⟩
      show (ρ.hom ≫ ρ.inv).base z = z
      rw [Iso.hom_inv_id]; rfl
    rw [← hrA, ← Set.image_univ]
    exact hunivA.image _ (pullback.fst M.toBase sA).base.hom.continuous.continuousOn
  exact ⟨h1, h2, h3, h4⟩

end S_AlgebraicCurve_SemistableModel_fibre_shapes_of_level
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_fibre_shapes_of_level (solution)
