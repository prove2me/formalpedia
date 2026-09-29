-- Prove2me | solution 1 for AlgebraicCurve.exists_closedPoint_specializes_reads_and_unique_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/67822a33-6eae-5332-ab79-7931916866b4

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_closedPoint_specializes_reads_and_unique_of_isProper

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DCaE133

noncomputable def toPlaceRing {L : Type} [Field L] (A : ValuationSubring L) {Fbar : Type} [Field Fbar]
    [Algebra (ResidueField ↥A) Fbar] (Q : Place (ResidueField ↥A) Fbar) : ↥A →+* ↥Q.toValuationSubring :=
  ((algebraMap (ResidueField ↥A) Fbar).comp (IsLocalRing.residue ↥A)).codRestrict Q.toValuationSubring.toSubring
    (fun a => Q.algebraMap_mem' _)

theorem toPlaceRing_apply {L : Type} [Field L] (A : ValuationSubring L) {Fbar : Type} [Field Fbar]
    [Algebra (ResidueField ↥A) Fbar] (Q : Place (ResidueField ↥A) Fbar) (a : ↥A) :
    ((toPlaceRing A Q a : ↥Q.toValuationSubring) : Fbar) = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) :=
  rfl

scoped instance isLocalHom_toPlaceRing {L : Type} [Field L] (A : ValuationSubring L) {Fbar : Type} [Field Fbar]
    [Algebra (ResidueField ↥A) Fbar] (Q : Place (ResidueField ↥A) Fbar) : IsLocalHom (toPlaceRing A Q) := by
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hna
  have h0 : toPlaceRing A Q a = 0 := by
    apply Subtype.ext
    rw [toPlaceRing_apply, (IsLocalRing.residue_eq_zero_iff _).mpr hm, map_zero]
    rfl
  rw [h0] at ha
  exact not_isUnit_zero ha

theorem stalkSpecializes_surjective_of_eq {X : Scheme} {y z : X} (h : y ⤳ z) (e : y = z) :
    Function.Surjective (X.presheaf.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  intro a
  exact ⟨a, rfl⟩

end DCaE133
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_closedPoint_specializes_reads_and_unique_of_isProper.DCaE133"

open DCaE133

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (η : X) (hη : toBase.base η = closedPoint ↥A) (hηnc : ∃ y : X, η ⤳ y ∧ y ≠ η)

    (hdim : ∀ y : X, η ⤳ y → y ≠ η → ∀ y' : X, y ⤳ y' → y' = y)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q : Place (ResidueField ↥A) Fbar) :
    (∃ x : X, toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧ η ⤳ x ∧ η ≠ x ∧
      (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)) ∧
    (∀ (Q' : Place (ResidueField ↥A) Fbar) (x₁ x₂ : X),
        toBase.base x₁ = closedPoint ↥A → (∀ y : X, x₁ ⤳ y → y = x₁) →
        toBase.base x₂ = closedPoint ↥A → (∀ y : X, x₂ ⤳ y → y = x₂) → η ⤳ x₁ → η ⤳ x₂ →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₁ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₂ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) →
          x₁ = x₂) := by
  classical

  let θ : ↑(X.presheaf.stalk η) →+* F := φ.symm.toRingHom.comp (algebraMap (X.presheaf.stalk η) X.functionField)
  have hθinj : Function.Injective θ :=
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk η) X.functionField)
  have hθrange : ∀ f : F, f ∈ R.integers ↔ ∃ s, θ s = f := by
    intro f
    rw [← ValuationSubring.mem_toSubring, hR]
    rfl
  have hθmem : ∀ s, θ s ∈ R.integers := fun s => (hθrange _).mpr ⟨s, rfl⟩
  let θR : ↑(X.presheaf.stalk η) →+* ↥R.integers :=
    { toFun := fun s => ⟨θ s, hθmem s⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun a b => Subtype.ext (map_mul θ a b)
      map_zero' := Subtype.ext (map_zero θ)
      map_add' := fun a b => Subtype.ext (map_add θ a b) }
  have hθR : ∀ s, (θR s : F) = θ s := fun s => rfl
  have hθRinj : Function.Injective θR := fun a b h => hθinj (by rw [← hθR, ← hθR, h])
  have hθRsurj : Function.Surjective θR := fun f => by
    obtain ⟨s, hs⟩ := (hθrange _).mp f.2
    exact ⟨s, Subtype.ext hs⟩
  have hθunit : ∀ s, IsUnit s ↔ IsUnit (θR s) := by
    intro s
    constructor
    · exact fun h => h.map θR
    · rintro ⟨w, hw⟩
      obtain ⟨s', hs'⟩ := hθRsurj ((w⁻¹ : (↥R.integers)ˣ) : ↥R.integers)
      refine isUnit_iff_exists_inv.mpr ⟨s', hθRinj ?_⟩
      rw [map_mul, map_one, hs', ← hw, Units.mul_inv]
  let ψ : ↑(X.presheaf.stalk η) →+* Fbar := R.residue.comp θR
  have hψ : ∀ s, ψ s = R.residue (θR s) := fun s => rfl
  have hψker : ∀ s, ψ s = 0 ↔ s ∈ maximalIdeal ↑(X.presheaf.stalk η) := by
    intro s
    rw [hψ, ← RingHom.mem_ker, R.ker_residue, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff, hθunit]
  haveI hψloc : IsLocalHom ψ := by
    constructor
    intro s hs
    by_contra hns
    have : ψ s = 0 := (hψker s).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hns)
    rw [this] at hs
    exact not_isUnit_zero hs
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨f, hf⟩ := R.residue_surjective y
    obtain ⟨s, hs⟩ := hθRsurj f
    exact ⟨s, by rw [hψ, hs, hf]⟩

  have key0 : ∀ a : ↥A, ψ ((X.presheaf.germ ⊤ η trivial) (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
      algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
    intro a
    have hθa : θ ((X.presheaf.germ ⊤ η trivial) (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
        algebraMap L F (a : L) := by
      show φ.symm (algebraMap _ _ ((X.presheaf.germ ⊤ η trivial) (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) = _
      have : (algebraMap (X.presheaf.stalk η) X.functionField) ((X.presheaf.germ ⊤ η trivial)
          (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
          SemistableModel.baseToFunctionField toBase a := by
        show (X.presheaf.germ ⊤ η trivial ≫ X.presheaf.stalkSpecializes _).hom _ = _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
        rfl
      rw [this, ← hφ, RingEquiv.symm_apply_apply]
    rw [hψ]
    have : θR ((X.presheaf.germ ⊤ η trivial) (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
        ⟨algebraMap L F (a : L), (R.algebraMap_mem_iff (a : L)).mpr a.2⟩ := Subtype.ext hθa
    rw [this, R.residue_algebraMap]

  have main : ∀ Q₀ : Place (ResidueField ↥A) Fbar, ∃ x : X, toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      η ⤳ x ∧ η ≠ x ∧
      (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q₀.toValuationSubring) ∧
      (∀ x' : X, (∀ y : X, x' ⤳ y → y = x') → η ⤳ x' →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x' → R.residue ⟨f, hf⟩ ∈ Q₀.toValuationSubring) →
        x' = x) := by
    intro Q₀

    let ρ := toPlaceRing A Q₀
    haveI hρloc : IsLocalHom (CommRingCat.ofHom ρ).hom := isLocalHom_toPlaceRing A Q₀
    let i₁ : Spec (CommRingCat.of Fbar) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk η
    let i₂ : Spec (CommRingCat.of ↥Q₀.toValuationSubring) ⟶ Spec (CommRingCat.of ↥A) := Spec.map (CommRingCat.ofHom ρ)
    have hsq : i₁ ≫ toBase =
        Spec.map (CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar)) ≫ i₂ := by

      have key : ∀ a : ↥A, ψ ((toBase.stalkMap η) (((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (toBase.base η) trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
        intro a
        rw [Scheme.Hom.germ_stalkMap_apply toBase ⊤ η trivial]
        have hθa : θ ((X.presheaf.germ (toBase ⁻¹ᵁ ⊤) η trivial) (toBase.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
            algebraMap L F (a : L) := by
          show φ.symm (algebraMap _ _ ((X.presheaf.germ ⊤ η trivial) (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) = _
          have : (algebraMap (X.presheaf.stalk η) X.functionField) ((X.presheaf.germ ⊤ η trivial)
              (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
              SemistableModel.baseToFunctionField toBase a := by
            show (X.presheaf.germ ⊤ η trivial ≫ X.presheaf.stalkSpecializes _).hom _ = _
            rw [TopCat.Presheaf.germ_stalkSpecializes]
            rfl
          rw [this, ← hφ, RingEquiv.symm_apply_apply]
        rw [hψ]
        have : θR ((X.presheaf.germ (toBase ⁻¹ᵁ ⊤) η trivial) (toBase.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
            ⟨algebraMap L F (a : L), (R.algebraMap_mem_iff (a : L)).mpr a.2⟩ := Subtype.ext hθa
        rw [this, R.residue_algebraMap]
      show Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk η ≫ toBase = _
      show _ = Spec.map (CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar)) ≫ Spec.map (CommRingCat.ofHom ρ)
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq]
      rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      show ψ ((toBase.stalkMap η) (((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (toBase.base η) trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) = ((ρ a : ↥Q₀.toValuationSubring) : Fbar)
      exact key a
    let S : ValuativeCommSq toBase :=
      { R := ↥Q₀.toValuationSubring, K := Fbar, i₁ := i₁, i₂ := i₂, commSq := ⟨hsq⟩ }
    have hE : ValuativeCriterion.Existence toBase := by
      have h := (inferInstance : UniversallyClosed toBase)
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar)) ≫ l = i₁ := hl₁
    have hl₂' : l ≫ toBase = i₂ := hl₂

    set x : X := l.base (closedPoint ↥Q₀.toValuationSubring) with hxdef
    have hi₁pt : ∀ p : Spec (CommRingCat.of Fbar), i₁.base p = η := by
      intro p
      show (X.fromSpecStalk η).base ((Spec.map (CommRingCat.ofHom ψ)).base p) = η
      have : (Spec.map (CommRingCat.ofHom ψ)).base p = closedPoint ↑(X.presheaf.stalk η) := by
        rw [show p = closedPoint Fbar from Subsingleton.elim _ _]
        exact Spec_closedPoint (f := CommRingCat.ofHom ψ)
      rw [this]
      exact Scheme.fromSpecStalk_closedPoint
    have hηx : η ⤳ x := by
      have h1 : η = l.base ((Spec.map (CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar))).base
          (closedPoint Fbar)) := by
        rw [← hi₁pt (closedPoint Fbar), ← hl₁']; rfl
      rw [h1]
      exact (IsLocalRing.specializes_closedPoint _).map l.base.hom.continuous
    have hx : toBase.base x = closedPoint ↥A := by
      show (l ≫ toBase).base (closedPoint _) = _
      rw [hl₂']
      exact Spec_closedPoint (f := CommRingCat.ofHom ρ)

    let g := Scheme.stalkClosedPointTo l
    have hlg : Spec.map g ≫ X.fromSpecStalk x = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have hC : g ≫ CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar) =
        X.presheaf.stalkSpecializes hηx ≫ CommRingCat.ofHom ψ := by
      have h1 : Spec.map (g ≫ CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar)) ≫ X.fromSpecStalk x = i₁ := by
        rw [Spec.map_comp, Category.assoc, hlg, hl₁']
      have h2 : Spec.map (X.presheaf.stalkSpecializes hηx ≫ CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x = i₁ := by
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
        rfl
      exact Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).mp (h1.trans h2.symm))
    have hCapp : ∀ s, ((g s : ↥Q₀.toValuationSubring) : Fbar) = ψ (X.presheaf.stalkSpecializes hηx s) := fun s =>
      congrFun (congrArg (fun k => ⇑(CommRingCat.Hom.hom k)) hC) s
    have hxη : η ≠ x := by
      intro e
      have hs : Function.Surjective (X.presheaf.stalkSpecializes hηx) := stalkSpecializes_surjective_of_eq hηx e
      apply Q₀.ne_top'
      rw [eq_top_iff]
      rintro y -
      obtain ⟨t, rfl⟩ := hψsurj y
      obtain ⟨s, rfl⟩ := hs t
      rw [← hCapp]
      exact (g s).2
    have hxc : ∀ y : X, x ⤳ y → y = x := hdim x hηx (Ne.symm hxη)

    have hθsp : ∀ {y : X} (hy : η ⤳ y) (s : X.presheaf.stalk y),
        θ (X.presheaf.stalkSpecializes hy s) = φ.symm (algebraMap (X.presheaf.stalk y) X.functionField s) := by
      intro y hy s
      show φ.symm ((X.presheaf.stalkSpecializes hy ≫ X.presheaf.stalkSpecializes _).hom s) = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    have hreads : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x →
        R.residue ⟨f, hf⟩ ∈ Q₀.toValuationSubring := by
      intro f hf hfx
      obtain ⟨s, hs⟩ := hfx
      have hθs : θ (X.presheaf.stalkSpecializes hηx s) = f := by rw [hθsp, ← hs]; rfl
      have : R.residue ⟨f, hf⟩ = ψ (X.presheaf.stalkSpecializes hηx s) := by
        rw [hψ]; congr 1; exact Subtype.ext hθs.symm
      rw [this, ← hCapp]
      exact (g s).2
    refine ⟨x, hx, hxc, hηx, hxη, hreads, ?_⟩

    intro x' hx'c hηx' hr'
    have hmem' : ∀ s : X.presheaf.stalk x', ψ (X.presheaf.stalkSpecializes hηx' s) ∈ Q₀.toValuationSubring := by
      intro s
      have hf : θ (X.presheaf.stalkSpecializes hηx' s) ∈ R.integers := hθmem _
      have hloc : θ (X.presheaf.stalkSpecializes hηx' s) ∈ SemistableModel.localRing X φ x' := ⟨s, (hθsp hηx' s).symm⟩
      have := hr' _ hf hloc
      rwa [hψ]
    let g' : ↑(X.presheaf.stalk x') →+* ↥Q₀.toValuationSubring :=
      (ψ.comp (X.presheaf.stalkSpecializes hηx').hom).codRestrict Q₀.toValuationSubring.toSubring hmem'
    have hg' : ∀ s, ((g' s : ↥Q₀.toValuationSubring) : Fbar) = ψ (X.presheaf.stalkSpecializes hηx' s) := fun s => rfl
    let l' : Spec (CommRingCat.of ↥Q₀.toValuationSubring) ⟶ X := Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecStalk x'
    have fac_left : Spec.map (CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar)) ≫ l' = i₁ := by
      show Spec.map (CommRingCat.ofHom (algebraMap ↥Q₀.toValuationSubring Fbar)) ≫ Spec.map (CommRingCat.ofHom g') ≫
        X.fromSpecStalk x' = Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk η
      rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hηx', ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      rfl
    have fac_right : l' ≫ toBase = i₂ := by
      show Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecStalk x' ≫ toBase = Spec.map (CommRingCat.ofHom ρ)
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      show ((g' ((toBase.stalkMap x') (((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (toBase.base x') trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) : ↥Q₀.toValuationSubring) : Fbar) = ((ρ a : ↥Q₀.toValuationSubring) : Fbar)
      rw [hg', Scheme.Hom.germ_stalkMap_apply toBase ⊤ x' trivial]
      show ψ ((X.presheaf.germ ⊤ x' trivial ≫ X.presheaf.stalkSpecializes hηx').hom
        (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      exact key0 a
    haveI : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion toBase S
    have heq : l' = l := congrArg CommSq.LiftStruct.l (Subsingleton.elim (⟨l', fac_left, fac_right⟩ : S.commSq.LiftStruct) ⟨l, hl₁, hl₂⟩)
    have hxx' : x ⤳ x' := by
      have : x ∈ Set.range (X.fromSpecStalk x').base := by
        refine ⟨(Spec.map (CommRingCat.ofHom g')).base (closedPoint _), ?_⟩
        show (Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecStalk x').base (closedPoint _) = x
        rw [show Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecStalk x' = l from heq]
      rw [Scheme.range_fromSpecStalk] at this
      exact this
    exact hxc x' hxx'

  obtain ⟨x, hx, hxc, hηx, hxη, hreads, -⟩ := main Q
  refine ⟨⟨x, hx, hxc, hηx, hxη, hreads⟩, ?_⟩
  intro Q' x₁ x₂ hx₁ hx₁c hx₂ hx₂c h₁ h₂ hr₁ hr₂
  obtain ⟨x', -, -, -, -, -, huniq⟩ := main Q'
  rw [huniq x₁ hx₁c h₁ hr₁, huniq x₂ hx₂c h₂ hr₂]

end S_AlgebraicCurve_exists_closedPoint_specializes_reads_and_unique_of_isProper
end P2MW
export P2MW.S_AlgebraicCurve_exists_closedPoint_specializes_reads_and_unique_of_isProper (solution)
