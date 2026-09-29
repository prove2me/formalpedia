-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.act_laws_of_forall_comp_eq_of_forall_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8f5b103a-71a2-5e47-8555-06146e20621d

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_act_laws_of_forall_comp_eq_of_forall_away

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

namespace C7LAWS

theorem mul_fst_congr' {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {x₁ y₁ : SchemeHomOver t₁ f} {x₂ y₂ : SchemeHomOver t₂ f} (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  rw [Subtype.ext hx, Subtype.ext hy]

theorem one_fst_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst ht; rfl

theorem eq_one_of_mul_self {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (e : SchemeHomOver t f)
    (h : L.mul t e e = e) : e = L.one t := by
  calc e = L.mul t (L.one t) e := (L.one_mul t e).symm
    _ = L.mul t (L.mul t (L.inv t e) e) e := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t e) (L.mul t e e) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t e) e := by rw [h]
    _ = L.one t := L.inv_mul_cancel t e

theorem tangentBase_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (k : Type) [Field k]
    (sk : S' →+* k) :
    tangentBase k (sk.comp φ) = tangentBase k sk ≫ Spec.map (CommRingCat.ofHom φ) := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem geomPoint_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (k : Type) [Field k]
    (sk : S' →+* k) :
    geomPoint k (sk.comp φ) = geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem tangentZero_tangentBase {S : Type} [CommRing S] (k : Type) [Field k] (sk : S →+* k) :
    tangentZero k ≫ tangentBase k sk = geomPoint k sk := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem tangentScale_tangentBase {S : Type} [CommRing S] (k : Type) [Field k] (sk : S →+* k) (c : k) :
    tangentScale k c ≫ tangentBase k sk = tangentBase k sk := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s <;> simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.map]

end C7LAWS

open C7LAWS in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    {d m : ℕ} {S : Type} [CommRing S] (X : PolarisedAbelianScheme 2 d m S)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (Xl : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (tl : ∀ i, QMStructure Λ star β (Xl i))
    (g : ∀ i, (Xl i).A ⟶ X.A)
    (hg : ∀ i, CategoryTheory.IsPullback (g i) (Xl i).f X.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (hgmul : ∀ (i : Fin k) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (x y : SchemeHomOver t' (Xl i).f),
      ((Xl i).L.mul t' x y).1 ≫ g i =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))
          ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (X.A ⟶ X.A)) (act_over : ∀ x : ↥Λ, act x ≫ X.f = X.f)
    (hact : ∀ (i : Fin k) (x : ↥Λ), (tl i).act x ≫ g i = g i ≫ act x) :
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
        pushPt (act x) (act_over x) (X.L.mul t P Q) =
          X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 X.A) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f),
        pushPt (act (x + y)) (act_over (x + y)) P =
          X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)) ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : S →+* k')
        (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) X.f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k' sk) X.f, P ∈ Set.range τ ↔ IsTangentVector X.L k' sk P) →
        (∀ v w : V, τ (v + w) = X.L.mul (tangentBase k' sk) (τ v) (τ w)) →
        (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k' V Φ = (n : k')) := by
  classical

  have hopen : ∀ i, IsOpenImmersion (g i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hg i).flip (IsOpenImmersion.of_isLocalization (r i))

  have hpt : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ i, s ∈ (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum S)) := by
    intro s
    have hx : ¬ (Set.range r ⊆ (s.asIdeal : Set S)) := by
      intro hsub
      have : (⊤ : Ideal S) ≤ s.asIdeal := hr ▸ Ideal.span_le.mpr hsub
      exact s.isPrime.ne_top (top_le_iff.mp this)
    obtain ⟨_, ⟨i, rfl⟩, hri⟩ := Set.not_subset.mp hx
    exact ⟨i, hri⟩
  have hcov : ∀ x : ↥X.A, ∃ (i : Fin k) (y : ↥(Xl i).A), (g i).base y = x := by
    intro x
    obtain ⟨i, hmem⟩ := hpt (X.f.base x)
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)] at hmem
    obtain ⟨s', hs'⟩ := hmem
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.f)
      (g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))) x s' hs'.symm
    refine ⟨i, ((hg i).isoPullback).inv.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, (hg i).isoPullback_inv_fst]
    exact hz1
  let 𝒰 : X.A.OpenCover := Scheme.Cover.mkOfCovers (Fin k) (fun i => (Xl i).A) g hcov (fun i => hopen i)
  have hact' : ∀ (i : Fin k) (x : ↥Λ) {Z : Scheme.{0}} (h : X.A ⟶ Z),
      (tl i).act x ≫ g i ≫ h = g i ≫ act x ≫ h := fun i x Z h => by rw [← Category.assoc, hact, Category.assoc]

  have hone : ∀ (i : Fin k) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i)))),
      ((Xl i).L.one t').1 ≫ g i = (X.L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))).1 := by
    intro i T t'
    let e' := (Xl i).L.one t'
    let eb : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))) X.f :=
      ⟨e'.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, e'.2]⟩
    have hee : X.L.mul _ eb eb = eb := by
      apply Subtype.ext
      have := hgmul i t' e' e'
      rw [(Xl i).L.one_mul] at this
      exact this.symm
    exact congrArg Subtype.val (eq_one_of_mul_self X.L _ eb hee)

  have chart : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (i : Fin k),
      ∃ τ : ((t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i)) : T.Opens) : Scheme.{0}) ⟶ Spec (CommRingCat.of (Localization.Away (r i))),
        τ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) = (t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι ≫ t := by
    intro T t i
    refine ⟨IsOpenImmersion.lift (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))
      ((t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι ≫ t) ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨y, rfl⟩
    have hy : t.base y.1 ∈ (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum S)) := y.2
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)] at hy
    obtain ⟨s', hs'⟩ := hy
    exact ⟨s', by rw [Scheme.Hom.comp_apply]; exact hs'⟩

  have liftPt : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (i : Fin k)
      {T' : Scheme.{0}} (τ : T' ⟶ Spec (CommRingCat.of (Localization.Away (r i)))) (ι : T' ⟶ T)
      (hι : τ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) = ι ≫ t)
      (P : SchemeHomOver t X.f),
      ∃ P' : SchemeHomOver τ (Xl i).f, P'.1 ≫ g i = ι ≫ P.1 := by
    intro T t i T' τ ι hι P
    have w : (ι ≫ P.1) ≫ X.f = τ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) := by
      rw [Category.assoc, P.2, hι]
    exact ⟨⟨(hg i).lift (ι ≫ P.1) τ w, (hg i).lift_snd _ _ _⟩, (hg i).lift_fst _ _ _⟩

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x T t P Q
    apply Subtype.ext
    let 𝒱 : T.OpenCover := Scheme.Cover.mkOfCovers (Fin k)
      (fun i => ((t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i)) : T.Opens) : Scheme.{0})) (fun i => (t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι)
      (fun y => by obtain ⟨i, hi⟩ := hpt (t.base y); exact ⟨i, ⟨y, hi⟩, rfl⟩)
    refine 𝒱.hom_ext _ _ fun i => ?_
    obtain ⟨τ, hτ⟩ := chart t i
    set ι := (t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι with hιdef
    show ι ≫ (pushPt (act x) (act_over x) (X.L.mul t P Q)).1 = ι ≫ (X.L.mul t _ _).1
    obtain ⟨P', hP'⟩ := liftPt i τ ι hτ P
    obtain ⟨Q', hQ'⟩ := liftPt i τ ι hτ Q
    have nat₁ := congrArg Subtype.val (X.L.mul_natural t (ι ≫ t) ι rfl P Q)
    have nat₂ := congrArg Subtype.val (X.L.mul_natural t (ι ≫ t) ι rfl (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))

    have lhs : ι ≫ (X.L.mul t P Q).1 ≫ act x = ((Xl i).L.mul τ (pushPt ((tl i).act x) ((tl i).act_over x) P')
        (pushPt ((tl i).act x) ((tl i).act_over x) Q')).1 ≫ g i := by
      rw [← Category.assoc]
      change (schemeHomOverComp ι rfl (X.L.mul t P Q)).1 ≫ act x = _
      rw [nat₁, ← congrArg Subtype.val ((tl i).act_hom x τ P' Q')]
      show _ = (((Xl i).L.mul τ P' Q').1 ≫ (tl i).act x) ≫ g i
      rw [Category.assoc, hact, ← Category.assoc, hgmul]
      congr 1
      exact mul_fst_congr' X.L hτ.symm hP'.symm hQ'.symm

    have rhs : ι ≫ (X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)).1 =
        ((Xl i).L.mul τ (pushPt ((tl i).act x) ((tl i).act_over x) P') (pushPt ((tl i).act x) ((tl i).act_over x) Q')).1 ≫ g i := by
      change (schemeHomOverComp ι rfl (X.L.mul t _ _)).1 = _
      rw [nat₂, hgmul]
      refine mul_fst_congr' X.L hτ.symm ?_ ?_
      · show ι ≫ P.1 ≫ act x = (P'.1 ≫ (tl i).act x) ≫ g i
        rw [Category.assoc, hact, ← Category.assoc, ← hP', Category.assoc]
      · show ι ≫ Q.1 ≫ act x = (Q'.1 ≫ (tl i).act x) ≫ g i
        rw [Category.assoc, hact, ← Category.assoc, ← hQ', Category.assoc]
    show ι ≫ (X.L.mul t P Q).1 ≫ act x = _
    rw [lhs, rhs]
  ·
    intro h
    apply 𝒰.hom_ext _ _ fun i => ?_
    show g i ≫ act ⟨1, h⟩ = g i ≫ 𝟙 X.A
    rw [← hact, (tl i).act_one h, Category.id_comp, Category.comp_id]
  ·
    intro x y h
    apply 𝒰.hom_ext _ _ fun i => ?_
    show g i ≫ act _ = g i ≫ act y ≫ act x
    rw [← hact, (tl i).act_mul x y h, Category.assoc, hact, ← Category.assoc, hact, Category.assoc]
  ·
    intro x y T t P
    apply Subtype.ext
    let 𝒱 : T.OpenCover := Scheme.Cover.mkOfCovers (Fin k)
      (fun i => ((t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i)) : T.Opens) : Scheme.{0})) (fun i => (t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι)
      (fun y => by obtain ⟨i, hi⟩ := hpt (t.base y); exact ⟨i, ⟨y, hi⟩, rfl⟩)
    refine 𝒱.hom_ext _ _ fun i => ?_
    obtain ⟨τ, hτ⟩ := chart t i
    set ι := (t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))).ι with hιdef
    obtain ⟨P', hP'⟩ := liftPt i τ ι hτ P
    have nat₂ := congrArg Subtype.val (X.L.mul_natural t (ι ≫ t) ι rfl (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    show ι ≫ P.1 ≫ act (x + y) = ι ≫ (X.L.mul t _ _).1
    have lhs : ι ≫ P.1 ≫ act (x + y) =
        ((Xl i).L.mul τ (pushPt ((tl i).act x) ((tl i).act_over x) P') (pushPt ((tl i).act y) ((tl i).act_over y) P')).1 ≫ g i := by
      rw [← Category.assoc, ← hP', Category.assoc, ← hact, ← Category.assoc]
      change (pushPt ((tl i).act (x + y)) ((tl i).act_over (x + y)) P').1 ≫ g i = _
      rw [congrArg Subtype.val ((tl i).act_add x y τ P')]
    have rhs : ι ≫ (X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)).1 =
        ((Xl i).L.mul τ (pushPt ((tl i).act x) ((tl i).act_over x) P') (pushPt ((tl i).act y) ((tl i).act_over y) P')).1 ≫ g i := by
      change (schemeHomOverComp ι rfl (X.L.mul t _ _)).1 = _
      rw [nat₂, hgmul]
      refine mul_fst_congr' X.L hτ.symm ?_ ?_
      · show ι ≫ P.1 ≫ act x = (P'.1 ≫ (tl i).act x) ≫ g i
        rw [Category.assoc, hact, ← Category.assoc, ← hP', Category.assoc]
      · show ι ≫ P.1 ≫ act y = (P'.1 ≫ (tl i).act y) ≫ g i
        rw [Category.assoc, hact, ← Category.assoc, ← hP', Category.assoc]
    rw [lhs, rhs]
  ·
    intro k' _ _ sk V _ _ _ τ hτinj hτrange hτadd hτsmul x Φ hΦ n hn

    obtain ⟨i, hunit⟩ : ∃ i, IsUnit (sk (r i)) := by
      by_contra hno
      push_neg at hno
      have hsub : Set.range r ⊆ (RingHom.ker sk : Set S) := by
        rintro _ ⟨i, rfl⟩
        exact (RingHom.mem_ker).mpr (not_ne_iff.mp fun h => hno i (isUnit_iff_ne_zero.mpr h))
      have htop : (⊤ : Ideal S) ≤ RingHom.ker sk := hr ▸ Ideal.span_le.mpr hsub
      have : (1 : S) ∈ RingHom.ker sk := htop trivial
      exact one_ne_zero ((map_one sk).symm.trans ((RingHom.mem_ker).mp this))
    let σ : Localization.Away (r i) →+* k' := IsLocalization.Away.lift (r i) (g := sk) hunit
    have hσ : σ.comp (algebraMap S (Localization.Away (r i))) = sk := IsLocalization.Away.lift_comp _ _
    have htb : tangentBase k' sk = tangentBase k' σ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) := by
      rw [← tangentBase_comp, hσ]
    have hgp : geomPoint k' sk = geomPoint k' σ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) := by
      rw [← geomPoint_comp, hσ]

    have w : ∀ v, (τ v).1 ≫ X.f = tangentBase k' σ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) :=
      fun v => by rw [(τ v).2, htb]
    let τl : V → SchemeHomOver (tangentBase k' σ) (Xl i).f := fun v =>
      ⟨(hg i).lift (τ v).1 (tangentBase k' σ) (w v), (hg i).lift_snd _ _ _⟩
    have hτl : ∀ v, (τl v).1 ≫ g i = (τ v).1 := fun v => (hg i).lift_fst _ _ _
    refine (tl i).act_trace k' σ V τl ?_ ?_ ?_ ?_ x Φ ?_ n hn
    · intro v w' hvw
      apply hτinj; apply Subtype.ext
      rw [← hτl, ← hτl, hvw]
    · intro P'
      constructor
      · rintro ⟨v, rfl⟩
        show tangentZero k' ≫ (τl v).1 = ((Xl i).L.one (geomPoint k' σ)).1
        apply (hg i).hom_ext
        · rw [Category.assoc, hτl, hone, ← one_fst_congr X.L hgp]
          exact (hτrange (τ v)).1 ⟨v, rfl⟩
        · rw [Category.assoc, (τl v).2, ((Xl i).L.one (geomPoint k' σ)).2, tangentZero_tangentBase]
      · intro hP'
        let P : SchemeHomOver (tangentBase k' sk) X.f :=
          ⟨P'.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P'.2, htb]⟩
        have hPt : IsTangentVector X.L k' sk P := by
          show tangentZero k' ≫ P'.1 ≫ g i = (X.L.one (geomPoint k' sk)).1
          rw [← Category.assoc, hP', hone, one_fst_congr X.L hgp]
        obtain ⟨v, hv⟩ := (hτrange P).2 hPt
        refine ⟨v, Subtype.ext ?_⟩
        apply (hg i).hom_ext
        · rw [hτl, hv]
        · rw [(τl v).2, P'.2]
    · intro v w'
      apply Subtype.ext
      apply (hg i).hom_ext
      · rw [hτl, hτadd, hgmul]
        exact mul_fst_congr' X.L htb (hτl v).symm (hτl w').symm
      · rw [(τl (v + w')).2, ((Xl i).L.mul (tangentBase k' σ) (τl v) (τl w')).2]
    · intro c v
      apply (hg i).hom_ext
      · rw [hτl, hτsmul, Category.assoc, hτl]
      · rw [(τl (c • v)).2, Category.assoc, (τl v).2, tangentScale_tangentBase]
    · intro v
      apply Subtype.ext
      apply (hg i).hom_ext
      · show (τl (Φ v)).1 ≫ g i = ((τl v).1 ≫ (tl i).act x) ≫ g i
        rw [hτl, hΦ v, Category.assoc, hact, ← Category.assoc, hτl]
        rfl
      · rw [(τl (Φ v)).2, (pushPt ((tl i).act x) ((tl i).act_over x) (τl v)).2]

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_act_laws_of_forall_comp_eq_of_forall_away
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_act_laws_of_forall_comp_eq_of_forall_away (solution)
