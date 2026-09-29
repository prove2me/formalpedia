-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/89ecc408-2ef6-584d-a390-5ebbac5a337d

import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite

namespace K1Sol

universe u

theorem not_mem_basicOpen_of_appLE_eq_zero {X : Scheme.{u}} {R : Type u} [CommRing R] [IsLocalRing R]
    (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (hrU : ⊤ ≤ r ⁻¹ᵁ U) (s : Γ(X, U))
    (h0 : (r.appLE U ⊤ hrU).hom s = 0) :
    r.base (IsLocalRing.closedPoint R) ∉ X.basicOpen s := by
  intro hmem
  have h : IsLocalRing.closedPoint R ∈ (Spec (CommRingCat.of R)).basicOpen ((r.appLE U ⊤ hrU).hom s) := by
    have := Scheme.basicOpen_appLE r ⊤ U hrU s
    rw [show (r.appLE U ⊤ hrU) s = (r.appLE U ⊤ hrU).hom s from rfl] at this
    rw [this]
    exact ⟨trivial, hmem⟩
  rw [h0, Scheme.basicOpen_zero] at h
  exact h

theorem ΓSpecIso_appLE_specMap_comp {Z : Scheme.{u}} {k Ω : Type u} [CommRing k] [CommRing Ω] (ι : k →+* Ω)
    (p : Spec (CommRingCat.of k) ⟶ Z) {U : Z.Opens} (e : ⊤ ≤ p ⁻¹ᵁ U)
    (e' : ⊤ ≤ (Spec.map (CommRingCat.ofHom ι) ≫ p) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (((Spec.map (CommRingCat.ofHom ι) ≫ p).appLE U ⊤ e').hom a) =
      ι ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((p.appLE U ⊤ e).hom a)) := by
  have hc : (Spec.map (CommRingCat.ofHom ι) ≫ p).appLE U ⊤ e' =
      p.appLE U ⊤ e ≫ (Spec.map (CommRingCat.ofHom ι)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ι)) p U ⊤ ⊤ e le_top).symm
  have hn := congrArg (fun φ => φ.hom ((p.appLE U ⊤ e).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ι))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [hc, CommRingCat.hom_comp, RingHom.comp_apply]
  exact hn

theorem ΓSpecIso_appLE_const {C : Scheme.{u}} {k : Type u} [CommRing k]
    (toBase : C ⟶ Spec (CommRingCat.of k)) (p : Spec (CommRingCat.of k) ⟶ C) (hp : p ≫ toBase = 𝟙 _)
    {U : C.Opens} (e : ⊤ ≤ p ⁻¹ᵁ U) (c : k) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((p.appLE U ⊤ e).hom
      ((C.presheaf.map (homOfLE (le_top (a := U))).op).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))) = c := by
  have h1 : C.presheaf.map (homOfLE (le_top (a := U))).op ≫ p.appLE U ⊤ e = p.appTop := by
    rw [Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appTop, Scheme.Hom.appLE]
  have h2 : toBase.appTop ≫ p.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
  have h1' := congrArg (fun φ => φ.hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) h1
  have h2' := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) h2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h1' h2'
  rw [h1', h2']
  have h3 := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h3
  exact h3

theorem sum_mul_eq_zero_of_place {k F' : Type u} [Field k] [Field F'] [Algebra k F'] (P : Place k F')
    {n : ℕ} (u v : Fin n → F') (c d : Fin n → k)
    (hu : ∀ i, ∃ a : ↥P.toValuationSubring, a ∈ IsLocalRing.maximalIdeal ↥P.toValuationSubring ∧
      u i = algebraMap k F' (c i) + (a : F'))
    (hv : ∀ i, ∃ b : ↥P.toValuationSubring, b ∈ IsLocalRing.maximalIdeal ↥P.toValuationSubring ∧
      v i = algebraMap k F' (d i) + (b : F'))
    (h : (∑ i, u i * v i) = 0) : (∑ i, c i * d i) = 0 := by
  classical
  choose a ha hua using hu
  choose b hb hvb using hv
  have hsum : (∑ i, (algebraMap k ↥P.toValuationSubring (c i) + a i) * (algebraMap k ↥P.toValuationSubring (d i) + b i)) = 0 := by
    apply Subtype.ext
    have : ((∑ i, (algebraMap k ↥P.toValuationSubring (c i) + a i) * (algebraMap k ↥P.toValuationSubring (d i) + b i) :
        ↥P.toValuationSubring) : F') = ∑ i, u i * v i := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hua i, hvb i, Place.coe_algebraMap, Place.coe_algebraMap]
    rw [this, h]; rfl
  have hres := congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥P.toValuationSubring)) hsum
  simp only [map_sum, map_mul, map_add, map_zero] at hres
  have ha0 : ∀ i, Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥P.toValuationSubring) (a i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (ha i)
  have hb0 : ∀ i, Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥P.toValuationSubring) (b i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hb i)
  simp only [ha0, hb0, add_zero] at hres
  have hmem : algebraMap k ↥P.toValuationSubring (∑ i, c i * d i) ∈ IsLocalRing.maximalIdeal ↥P.toValuationSubring := by
    rw [map_sum, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    simp only [map_mul]
    exact hres
  by_contra hne
  have hunit : IsUnit (algebraMap k ↥P.toValuationSubring (∑ i, c i * d i)) := (IsUnit.mk0 _ hne).map _
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit

theorem inv_mem_of_isUnit {F' : Type u} [Field F'] (S : ValuationSubring F') (x : ↥S) (hx : IsUnit x) :
    ((x : F')⁻¹) ∈ S := by
  obtain ⟨w, hw⟩ := hx
  have h1 : ((w⁻¹ : (↥S)ˣ) : ↥S) * x = 1 := by rw [← hw, Units.inv_mul]
  have h2 : (((w⁻¹ : (↥S)ˣ) : ↥S) : F') * (x : F') = 1 := by
    have := congrArg (Subtype.val) h1
    simpa using this
  rw [← (eq_inv_of_mul_eq_one_left h2)]
  exact Subtype.mem _

theorem exists_mem_maximalIdeal_map_eq {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') (z : F) (c : k)
    (hz : ∃ a : ↥(P.restrictAlong φ hφ).toValuationSubring,
      a ∈ IsLocalRing.maximalIdeal ↥(P.restrictAlong φ hφ).toValuationSubring ∧ z = algebraMap k F c + (a : F)) :
    ∃ a' : ↥P.toValuationSubring, a' ∈ IsLocalRing.maximalIdeal ↥P.toValuationSubring ∧
      φ z = algebraMap k F' c + (a' : F') := by
  obtain ⟨a, ha, hza⟩ := hz
  have hmem : ∀ w : F, w ∈ (P.restrictAlong φ hφ).toValuationSubring ↔ φ w ∈ P.toValuationSubring := fun w => Iff.rfl
  refine ⟨⟨φ (a : F), (hmem _).mp a.2⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    apply (IsLocalRing.mem_maximalIdeal _).mp ha
    have ha0 : (a : F) ≠ 0 := by
      intro h0
      apply not_isUnit_zero (M₀ := ↥P.toValuationSubring)
      have : (⟨φ (a : F), (hmem _).mp a.2⟩ : ↥P.toValuationSubring) = 0 := Subtype.ext (by simp [h0])
      rwa [this] at hunit
    have hinv' := inv_mem_of_isUnit _ _ hunit
    have hinv : (a : F)⁻¹ ∈ (P.restrictAlong φ hφ).toValuationSubring := by
      rw [hmem, map_inv₀]; exact hinv'
    exact ⟨⟨a, ⟨(a : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩
  · rw [hza, map_add, AlgHom.commutes]

theorem ΓSpecIso_hom_injective (R : CommRingCat.{u}) : Function.Injective (Scheme.ΓSpecIso R).hom.hom := by
  intro a b h
  have := congrArg ((Scheme.ΓSpecIso R).inv.hom) h
  have e1 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso R).hom_inv_id
  have e2 := congrArg (fun φ => φ.hom b) (Scheme.ΓSpecIso R).hom_inv_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at e1 e2
  rw [e1, e2] at this; exact this

theorem exists_mem_maximalIdeal_of_germ_eq {k : Type u} [Field k] [IsAlgClosed k] {F : Type u} [Field F] [Algebra k F]
    (𝔐 : AlgebraicCurve.CurveModel k F) (Q : Place k F) {U : 𝔐.C.Opens} (hU : genericPoint 𝔐.C ∈ U)
    (hq : ⊤ ≤ (𝔐.pointEquivPlace.symm Q).1 ⁻¹ᵁ U)
    (s : Γ(𝔐.C, U)) (z : F) (hs : (𝔐.C.presheaf.germ U (genericPoint 𝔐.C) hU).hom s = 𝔐.ffEquiv z) :
    ∃ a : ↥Q.toValuationSubring, a ∈ IsLocalRing.maximalIdeal ↥Q.toValuationSubring ∧
      z = algebraMap k F ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        ((((𝔐.pointEquivPlace.symm Q).1).appLE U ⊤ hq).hom s)) + (a : F) := by

  generalize hc : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((((𝔐.pointEquivPlace.symm Q).1).appLE U ⊤ hq).hom s) = c
  have hq' : ((𝔐.pointEquivPlace.symm Q).1).base (IsLocalRing.closedPoint k) ∈ U := hq (Set.mem_univ _)

  have hQ : 𝔐.placeOfPoint (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm Q)) = Q := by
    rw [← AlgebraicCurve.CurveModel.pointEquivPlace_apply]; exact Equiv.apply_symm_apply _ _
  have hx₀ : ((pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm Q)) : ↥𝔐.C) =
      ((𝔐.pointEquivPlace.symm Q).1).base (IsLocalRing.closedPoint k) := rfl
  have hrange := 𝔐.range_stalk_eq (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm Q))
  rw [hQ] at hrange
  have hmemQ : ∀ g : ↑(𝔐.C.presheaf.stalk (((𝔐.pointEquivPlace.symm Q).1).base (IsLocalRing.closedPoint k))),
      𝔐.ffEquiv.symm (algebraMap _ ↑𝔐.C.functionField g) ∈ Q.toValuationSubring := by
    intro g
    have : 𝔐.ffEquiv.symm (algebraMap _ ↑𝔐.C.functionField g) ∈ Q.toValuationSubring.toSubring := by
      rw [← hrange]; exact ⟨g, rfl⟩
    exact this
  have hsurj : ∀ w : F, w ∈ Q.toValuationSubring →
      ∃ g : ↑(𝔐.C.presheaf.stalk (((𝔐.pointEquivPlace.symm Q).1).base (IsLocalRing.closedPoint k))),
        𝔐.ffEquiv.symm (algebraMap _ ↑𝔐.C.functionField g) = w := by
    intro w hw
    have : w ∈ Q.toValuationSubring.toSubring := hw
    rw [← hrange] at this
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩

  have hspec : ∀ s' : Γ(𝔐.C, U), algebraMap _ ↑𝔐.C.functionField
      ((𝔐.C.presheaf.germ U _ hq').hom s') = (𝔐.C.presheaf.germ U (genericPoint 𝔐.C) hU).hom s' := by
    intro s'
    show (𝔐.C.presheaf.stalkSpecializes (genericPoint_specializes _)).hom ((𝔐.C.presheaf.germ U _ hq').hom s') = _
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

  have hcst_germ : (𝔐.C.presheaf.germ U (genericPoint 𝔐.C) hU).hom
      ((𝔐.C.presheaf.map (homOfLE (le_top (a := U))).op).hom (𝔐.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) =
      𝔐.ffEquiv (algebraMap k F c) := by
    rw [𝔐.ffEquiv_algebraMap]
    exact TopCat.Presheaf.germ_res_apply 𝔐.C.presheaf (homOfLE (le_top (a := U))) _ hU _
  have hcst_eval := ΓSpecIso_appLE_const 𝔐.toBase (𝔐.pointEquivPlace.symm Q).1 (𝔐.pointEquivPlace.symm Q).2 hq c

  have h0 : (((𝔐.pointEquivPlace.symm Q).1).appLE U ⊤ hq).hom
      (s - (𝔐.C.presheaf.map (homOfLE (le_top (a := U))).op).hom (𝔐.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) = 0 := by
    apply ΓSpecIso_hom_injective
    rw [map_sub, map_sub, map_zero, hcst_eval, hc, sub_self]
  have hnu : ¬ IsUnit ((𝔐.C.presheaf.germ U _ hq').hom
      (s - (𝔐.C.presheaf.map (homOfLE (le_top (a := U))).op).hom (𝔐.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))) := by
    intro hu
    exact not_mem_basicOpen_of_appLE_eq_zero _ hq _ h0 ((Scheme.mem_basicOpen _ _ _ hq').mpr hu)

  have hz : 𝔐.ffEquiv.symm (algebraMap _ ↑𝔐.C.functionField ((𝔐.C.presheaf.germ U _ hq').hom
      (s - (𝔐.C.presheaf.map (homOfLE (le_top (a := U))).op).hom (𝔐.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))))) =
      z - algebraMap k F c := by
    rw [hspec, map_sub, hs, hcst_germ, map_sub, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  refine ⟨⟨z - algebraMap k F c, hz ▸ hmemQ _⟩, ?_, by ring⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hnu
  have hz0 : z - algebraMap k F c ≠ 0 := by
    intro h0'
    apply not_isUnit_zero (M₀ := ↥Q.toValuationSubring)
    have : (⟨z - algebraMap k F c, hz ▸ hmemQ _⟩ : ↥Q.toValuationSubring) = 0 := Subtype.ext h0'
    rwa [this] at hu
  have hi : (z - algebraMap k F c)⁻¹ ∈ Q.toValuationSubring := inv_mem_of_isUnit _ _ hu
  obtain ⟨g, hg⟩ := hsurj _ hi
  have hmul : algebraMap _ ↑𝔐.C.functionField ((𝔐.C.presheaf.germ U _ hq').hom
      (s - (𝔐.C.presheaf.map (homOfLE (le_top (a := U))).op).hom (𝔐.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) * g) = 1 := by
    apply 𝔐.ffEquiv.symm.injective
    rw [map_mul, map_mul, hg, hz]
    simp only [map_one]
    first
      | exact mul_inv_cancel₀ hz0
      | (rw [map_one]; exact mul_inv_cancel₀ hz0)
  have hinjK := IsFractionRing.injective
    ↑(𝔐.C.presheaf.stalk (((𝔐.pointEquivPlace.symm Q).1).base (IsLocalRing.closedPoint k))) ↑𝔐.C.functionField
  exact IsUnit.of_mul_eq_one g (hinjK (by rw [hmul, map_one]))

end K1Sol

open K1Sol in
theorem solution
    {k : Type} [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F]
    (𝔐 : AlgebraicCurve.CurveModel k F)
    {F' : Type} [Field F'] [Algebra k F']
    (φ₀ φ₁ : F →ₐ[k] F') (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (θ : X ⟶ 𝔐.C) (hθ : IsOpenMap θ.base)
    (d₀ d₁ : Y ⟶ X)
    (hdom₀ : d₀.base (genericPoint Y) = genericPoint X)
    (hdom₁ : d₁.base (genericPoint Y) = genericPoint X)
    (j : F →+* ↑X.functionField)
    (hpin : ∀ (z : F) (U : 𝔐.C.Opens) (hU : genericPoint 𝔐.C ∈ U) (hU' : genericPoint X ∈ θ ⁻¹ᵁ U)
      (sec : 𝔐.C.presheaf.obj (Opposite.op U)),
      (𝔐.C.presheaf.germ U (genericPoint 𝔐.C) hU).hom sec = 𝔐.ffEquiv z →
      (X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X) hU').hom ((θ.app U).hom sec) = j z)
    (δ₀ δ₁ : ↑X.functionField →+* ↑Y.functionField)
    (hδ₀ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ d₀ ⁻¹ᵁ U) (sec : X.presheaf.obj (Opposite.op U)),
      δ₀ ((X.presheaf.germ U (genericPoint X) hU).hom sec) = (Y.presheaf.germ (d₀ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((d₀.app U).hom sec))
    (hδ₁ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ d₁ ⁻¹ᵁ U) (sec : X.presheaf.obj (Opposite.op U)),
      δ₁ ((X.presheaf.germ U (genericPoint X) hU).hom sec) = (Y.presheaf.germ (d₁ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((d₁.app U).hom sec))
    (Ω : Type) [Field Ω] (ι : k →+* Ω)
    (hD : Dense {y : ↥Y | ∃ (y' : Spec (CommRingCat.of Ω) ⟶ Y) (P : Place k F'),
      y'.base (IsLocalRing.closedPoint Ω) = y ∧
      y' ≫ d₀ ≫ θ = Spec.map (CommRingCat.ofHom ι) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong φ₀ hφ₀)).1 ∧
      y' ≫ d₁ ≫ θ = Spec.map (CommRingCat.ofHom ι) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong φ₁ hφ₁)).1}) :
    ∀ (n : ℕ) (x y : Fin n → F),
      (∑ i, φ₀ (x i) * φ₁ (y i)) = 0 → (∑ i, δ₀ (j (x i)) * δ₁ (j (y i))) = 0 := by
  intro n x y hrel
  classical

  have hθgen : θ.base (genericPoint X) = genericPoint 𝔐.C := by
    apply ((genericPoint_spec 𝔐.C).eq _).symm
    convert! (genericPoint_spec X).image θ.continuous
    symm
    rw [← Set.univ_subset_iff]
    convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ hθ.isOpen_range _
    · rw [Set.univ_inter, Set.image_univ]
    · apply PreirreducibleSpace.isPreirreducible_univ
    · exact ⟨_, trivial, Set.mem_range_self (genericPoint X)⟩

  have hsec : ∀ z : F, ∃ (U : 𝔐.C.Opens) (hU : genericPoint 𝔐.C ∈ U) (s : Γ(𝔐.C, U)),
      (𝔐.C.presheaf.germ U (genericPoint 𝔐.C) hU).hom s = 𝔐.ffEquiv z := fun z =>
    TopCat.Presheaf.germ_exist 𝔐.C.presheaf (x := genericPoint 𝔐.C) (𝔐.ffEquiv z)
  choose U hU s hs using fun i : Fin n => hsec (x i)
  choose V hV t ht using fun i : Fin n => hsec (y i)
  have hd₀θ : (d₀ ≫ θ).base (genericPoint Y) = genericPoint 𝔐.C := by
    show θ.base (d₀.base (genericPoint Y)) = _
    rw [hdom₀, hθgen]
  have hd₁θ : (d₁ ≫ θ).base (genericPoint Y) = genericPoint 𝔐.C := by
    show θ.base (d₁.base (genericPoint Y)) = _
    rw [hdom₁, hθgen]
  have hmem₀ : ∀ i, genericPoint Y ∈ (d₀ ≫ θ) ⁻¹ᵁ (U i) := fun i => by
    show (d₀ ≫ θ).base (genericPoint Y) ∈ U i
    rw [hd₀θ]; exact hU i
  have hmem₁ : ∀ i, genericPoint Y ∈ (d₁ ≫ θ) ⁻¹ᵁ (V i) := fun i => by
    show (d₁ ≫ θ).base (genericPoint Y) ∈ V i
    rw [hd₁θ]; exact hV i

  have hξW : genericPoint Y ∈ (Finset.univ : Finset (Fin n)).inf (fun i => (d₀ ≫ θ) ⁻¹ᵁ (U i) ⊓ (d₁ ≫ θ) ⁻¹ᵁ (V i)) := by
    have : ∀ S : Finset (Fin n), genericPoint Y ∈ S.inf (fun i => (d₀ ≫ θ) ⁻¹ᵁ (U i) ⊓ (d₁ ≫ θ) ⁻¹ᵁ (V i)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => rw [Finset.inf_empty]; trivial
      | insert a S ha ih => rw [Finset.inf_insert]; exact ⟨⟨hmem₀ a, hmem₁ a⟩, ih⟩
    exact this _
  set W : Y.Opens := (Finset.univ : Finset (Fin n)).inf (fun i => (d₀ ≫ θ) ⁻¹ᵁ (U i) ⊓ (d₁ ≫ θ) ⁻¹ᵁ (V i)) with hWdef
  have hW₀ : ∀ i, W ≤ (d₀ ≫ θ) ⁻¹ᵁ (U i) := fun i => by
    rw [hWdef]; exact (Finset.inf_le (Finset.mem_univ i)).trans inf_le_left
  have hW₁ : ∀ i, W ≤ (d₁ ≫ θ) ⁻¹ᵁ (V i) := fun i => by
    rw [hWdef]; exact (Finset.inf_le (Finset.mem_univ i)).trans inf_le_right
  haveI : Nonempty ↥W := ⟨⟨_, hξW⟩⟩

  have hgerm₀ : ∀ i, (Y.presheaf.germ W (genericPoint Y) hξW).hom
      ((Y.presheaf.map (homOfLE (hW₀ i)).op).hom (((d₀ ≫ θ).app (U i)).hom (s i))) = δ₀ (j (x i)) := by
    intro i
    have hUX : genericPoint X ∈ θ ⁻¹ᵁ (U i) := by
      show θ.base _ ∈ U i
      rw [hθgen]; exact hU i
    rw [show (Y.presheaf.germ W (genericPoint Y) hξW).hom ((Y.presheaf.map (homOfLE (hW₀ i)).op).hom (((d₀ ≫ θ).app (U i)).hom (s i))) =
        (Y.presheaf.germ ((d₀ ≫ θ) ⁻¹ᵁ (U i)) (genericPoint Y) (hmem₀ i)).hom (((d₀ ≫ θ).app (U i)).hom (s i)) from
        TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (hW₀ i)) _ hξW _]
    have h1 := hpin (x i) (U i) (hU i) hUX (s i) (hs i)
    have h2 := hδ₀ (θ ⁻¹ᵁ (U i)) hUX (hmem₀ i) ((θ.app (U i)).hom (s i))
    rw [h1] at h2
    exact h2.symm
  have hgerm₁ : ∀ i, (Y.presheaf.germ W (genericPoint Y) hξW).hom
      ((Y.presheaf.map (homOfLE (hW₁ i)).op).hom (((d₁ ≫ θ).app (V i)).hom (t i))) = δ₁ (j (y i)) := by
    intro i
    have hUX : genericPoint X ∈ θ ⁻¹ᵁ (V i) := by
      show θ.base _ ∈ V i
      rw [hθgen]; exact hV i
    rw [show (Y.presheaf.germ W (genericPoint Y) hξW).hom ((Y.presheaf.map (homOfLE (hW₁ i)).op).hom (((d₁ ≫ θ).app (V i)).hom (t i))) =
        (Y.presheaf.germ ((d₁ ≫ θ) ⁻¹ᵁ (V i)) (genericPoint Y) (hmem₁ i)).hom (((d₁ ≫ θ).app (V i)).hom (t i)) from
        TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (hW₁ i)) _ hξW _]
    have h1 := hpin (y i) (V i) (hV i) hUX (t i) (ht i)
    have h2 := hδ₁ (θ ⁻¹ᵁ (V i)) hUX (hmem₁ i) ((θ.app (V i)).hom (t i))
    rw [h1] at h2
    exact h2.symm

  set G : Γ(Y, W) := ∑ i, (Y.presheaf.map (homOfLE (hW₀ i)).op).hom (((d₀ ≫ θ).app (U i)).hom (s i)) *
      (Y.presheaf.map (homOfLE (hW₁ i)).op).hom (((d₁ ≫ θ).app (V i)).hom (t i)) with hGdef
  have hG : (Y.presheaf.germ W (genericPoint Y) hξW).hom G = ∑ i, δ₀ (j (x i)) * δ₁ (j (y i)) := by
    rw [hGdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hgerm₀, hgerm₁]
  by_contra hne
  have hG0 : G ≠ 0 := by
    intro h; apply hne; rw [← hG, h, map_zero]
  have hbo : ((Y.basicOpen G : Y.Opens) : Set ↥Y).Nonempty := by
    by_contra h
    apply hG0
    apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot
    exact le_bot_iff.mp fun z hz => (h ⟨z, hz⟩).elim
  obtain ⟨yy, hyD, hyG⟩ := hD.exists_mem_open (Y.basicOpen G).isOpen hbo
  obtain ⟨y', P, hyy, hy₀, hy₁⟩ := hyD
  subst hyy
  have hyW : y'.base (IsLocalRing.closedPoint Ω) ∈ W := Y.basicOpen_le G hyG
  have hptk : ∀ z : ↥(Spec (CommRingCat.of k)), z = IsLocalRing.closedPoint k := fun z => Subsingleton.elim _ _
  have hptΩ : ∀ z : ↥(Spec (CommRingCat.of Ω)), z = IsLocalRing.closedPoint Ω := fun z => Subsingleton.elim _ _
  have hy'W : ⊤ ≤ y' ⁻¹ᵁ W := fun z _ => by rw [hptΩ z]; exact hyW

  have hq₀ : ∀ i, ⊤ ≤ ((𝔐.pointEquivPlace.symm (P.restrictAlong φ₀ hφ₀)).1) ⁻¹ᵁ (U i) := by
    intro i z _
    rw [hptk z]
    have h1 : (y' ≫ d₀ ≫ θ).base (IsLocalRing.closedPoint Ω) ∈ U i := hW₀ i hyW
    rw [hy₀] at h1
    have h2 : ((𝔐.pointEquivPlace.symm (P.restrictAlong φ₀ hφ₀)).1).base
        ((Spec.map (CommRingCat.ofHom ι)).base (IsLocalRing.closedPoint Ω)) ∈ U i := h1
    rwa [hptk ((Spec.map (CommRingCat.ofHom ι)).base (IsLocalRing.closedPoint Ω))] at h2
  have hq₁ : ∀ i, ⊤ ≤ ((𝔐.pointEquivPlace.symm (P.restrictAlong φ₁ hφ₁)).1) ⁻¹ᵁ (V i) := by
    intro i z _
    rw [hptk z]
    have h1 : (y' ≫ d₁ ≫ θ).base (IsLocalRing.closedPoint Ω) ∈ V i := hW₁ i hyW
    rw [hy₁] at h1
    have h2 : ((𝔐.pointEquivPlace.symm (P.restrictAlong φ₁ hφ₁)).1).base
        ((Spec.map (CommRingCat.ofHom ι)).base (IsLocalRing.closedPoint Ω)) ∈ V i := h1
    rwa [hptk ((Spec.map (CommRingCat.ofHom ι)).base (IsLocalRing.closedPoint Ω))] at h2

  set c : Fin n → k := fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((((𝔐.pointEquivPlace.symm (P.restrictAlong φ₀ hφ₀)).1).appLE (U i) ⊤ (hq₀ i)).hom (s i)) with hcdef
  set dd : Fin n → k := fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((((𝔐.pointEquivPlace.symm (P.restrictAlong φ₁ hφ₁)).1).appLE (V i) ⊤ (hq₁ i)).hom (t i)) with hdddef

  have hx' : ∀ i, ∃ a : ↥P.toValuationSubring, a ∈ IsLocalRing.maximalIdeal ↥P.toValuationSubring ∧
      φ₀ (x i) = algebraMap k F' (c i) + (a : F') := fun i =>
    exists_mem_maximalIdeal_map_eq φ₀ hφ₀ P (x i) (c i)
      (exists_mem_maximalIdeal_of_germ_eq 𝔐 (P.restrictAlong φ₀ hφ₀) (hU i) (hq₀ i) (s i) (x i) (hs i))
  have hy' : ∀ i, ∃ b : ↥P.toValuationSubring, b ∈ IsLocalRing.maximalIdeal ↥P.toValuationSubring ∧
      φ₁ (y i) = algebraMap k F' (dd i) + (b : F') := fun i =>
    exists_mem_maximalIdeal_map_eq φ₁ hφ₁ P (y i) (dd i)
      (exists_mem_maximalIdeal_of_germ_eq 𝔐 (P.restrictAlong φ₁ hφ₁) (hV i) (hq₁ i) (t i) (y i) (ht i))
  have hcd : (∑ i, c i * dd i) = 0 :=
    sum_mul_eq_zero_of_place P (fun i => φ₀ (x i)) (fun i => φ₁ (y i)) c dd hx' hy' hrel

  have hval₀ : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((y'.appLE W ⊤ hy'W).hom
      ((Y.presheaf.map (homOfLE (hW₀ i)).op).hom (((d₀ ≫ θ).app (U i)).hom (s i)))) = ι (c i) := by
    intro i
    have e0 := congrArg (fun φ => φ.hom (((d₀ ≫ θ).app (U i)).hom (s i))) (Scheme.Hom.map_appLE y' hy'W (homOfLE (hW₀ i)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e0
    rw [e0]
    have hc := Scheme.Hom.appLE_comp_appLE y' (d₀ ≫ θ) (U i) ((d₀ ≫ θ) ⁻¹ᵁ (U i)) ⊤ le_rfl (fun z hz => hW₀ i (hy'W hz))
    rw [Scheme.Hom.appLE_eq_app] at hc
    have hc' := congrArg (fun φ => φ.hom (s i)) hc
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc'
    rw [hc']
    have key : ∀ (r : Spec (CommRingCat.of Ω) ⟶ 𝔐.C)
        (hr : r = Spec.map (CommRingCat.ofHom ι) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong φ₀ hφ₀)).1)
        (e : ⊤ ≤ r ⁻¹ᵁ (U i)),
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((r.appLE (U i) ⊤ e).hom (s i)) = ι (c i) := by
      intro r hr e; subst hr
      exact ΓSpecIso_appLE_specMap_comp ι _ (hq₀ i) e (s i)
    exact key _ hy₀ _
  have hval₁ : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((y'.appLE W ⊤ hy'W).hom
      ((Y.presheaf.map (homOfLE (hW₁ i)).op).hom (((d₁ ≫ θ).app (V i)).hom (t i)))) = ι (dd i) := by
    intro i
    have e0 := congrArg (fun φ => φ.hom (((d₁ ≫ θ).app (V i)).hom (t i))) (Scheme.Hom.map_appLE y' hy'W (homOfLE (hW₁ i)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e0
    rw [e0]
    have hc := Scheme.Hom.appLE_comp_appLE y' (d₁ ≫ θ) (V i) ((d₁ ≫ θ) ⁻¹ᵁ (V i)) ⊤ le_rfl (fun z hz => hW₁ i (hy'W hz))
    rw [Scheme.Hom.appLE_eq_app] at hc
    have hc' := congrArg (fun φ => φ.hom (t i)) hc
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc'
    rw [hc']
    have key : ∀ (r : Spec (CommRingCat.of Ω) ⟶ 𝔐.C)
        (hr : r = Spec.map (CommRingCat.ofHom ι) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong φ₁ hφ₁)).1)
        (e : ⊤ ≤ r ⁻¹ᵁ (V i)),
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((r.appLE (V i) ⊤ e).hom (t i)) = ι (dd i) := by
      intro r hr e; subst hr
      exact ΓSpecIso_appLE_specMap_comp ι _ (hq₁ i) e (t i)
    exact key _ hy₁ _
  have hGval : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((y'.appLE W ⊤ hy'W).hom G) = ι (∑ i, c i * dd i) := by
    rw [map_sum ι, hGdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_mul, hval₀, hval₁]
  have h0 : (y'.appLE W ⊤ hy'W).hom G = 0 := by
    apply ΓSpecIso_hom_injective
    rw [hGval, hcd, map_zero, map_zero]
  exact not_mem_basicOpen_of_appLE_eq_zero y' hy'W G h0 hyG

end S_AlgebraicCurve_CurveModel_sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_sum_mul_eq_zero_of_sum_mul_eq_zero_of_dense_of_germ_eq (solution)
