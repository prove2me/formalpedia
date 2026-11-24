-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:00.635055+00:00
-- url     : https://prove2.me/theorems/55711ca0-984c-4575-ac2d-ca92fa3efdbb
-- title:
--   Exists Valuation Subring Dominating Subring
-- statement:
--   Definitions and structural lemmas for Exists Valuation Subring Dominating Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
namespace GlobalTheory
abbrev specAlgebraMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))
theorem specAlgebraMap_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    specAlgebraMap B C ≫ specAlgebraMap A B = specAlgebraMap A C := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
section Extension
variable {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {X X' S S' : Scheme.{u}}
theorem exists_valuativeExtension (p : X ⟶ S) [UniversallyClosed p] (r : Spec (.of V) ⟶ S)
    (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r) :
    ∃ x : Spec (.of V) ⟶ X, specAlgebraMap V K ≫ x = y ∧ x ≫ p = r := by
  have hE : ValuativeCriterion.Existence p := by
    have h : UniversallyClosed p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := y, i₂ := r, commSq := ⟨h⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩
variable (K) in

theorem valuativePoint_ext (p : X ⟶ S) [IsSeparated p] {x x' : Spec (.of V) ⟶ X}
    (h : specAlgebraMap V K ≫ x = specAlgebraMap V K ≫ x') (h' : x ≫ p = x' ≫ p) : x = x' := by
  have hU := IsSeparated.valuativeCriterion p
    { R := V, K := K, i₁ := specAlgebraMap V K ≫ x, i₂ := x ≫ p,
      commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg (fun l ↦ l.l) (hU.elim ⟨x, rfl, rfl⟩ ⟨x', h.symm, h'.symm⟩)
variable (K) in

theorem valuativePoint_ext_of_isSeparated [X.IsSeparated] {x x' : Spec (.of V) ⟶ X}
    (h : specAlgebraMap V K ≫ x = specAlgebraMap V K ≫ x') : x = x' :=
  valuativePoint_ext K (terminal.from X) h (terminal.hom_ext _ _)
theorem existsUnique_valuativeExtension (p : X ⟶ S) [UniversallyClosed p] [IsSeparated p]
    (r : Spec (.of V) ⟶ S) (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r) :
    ∃! x : Spec (.of V) ⟶ X, specAlgebraMap V K ≫ x = y ∧ x ≫ p = r := by
  obtain ⟨x, hx⟩ := exists_valuativeExtension p r y h
  exact ⟨x, hx, fun x' hx' ↦
    valuativePoint_ext K p (hx'.1.trans hx.1.symm) (hx'.2.trans hx.2.symm)⟩
def valExt (p : X ⟶ S) [UniversallyClosed p] [IsSeparated p] (r : Spec (.of V) ⟶ S)
    (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r) : Spec (.of V) ⟶ X :=
  (existsUnique_valuativeExtension p r y h).exists.choose
variable (p : X ⟶ S) [UniversallyClosed p] [IsSeparated p] (r : Spec (.of V) ⟶ S)
  (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r)
@[reassoc (attr := simp)]
theorem specAlgebraMap_valExt : specAlgebraMap V K ≫ valExt p r y h = y :=
  (existsUnique_valuativeExtension p r y h).exists.choose_spec.1
@[reassoc (attr := simp)]
theorem valExt_over : valExt p r y h ≫ p = r :=
  (existsUnique_valuativeExtension p r y h).exists.choose_spec.2
theorem eq_valExt_iff (x : Spec (.of V) ⟶ X) :
    x = valExt p r y h ↔ specAlgebraMap V K ≫ x = y ∧ x ≫ p = r :=
  ⟨fun e ↦ e ▸ ⟨specAlgebraMap_valExt p r y h, valExt_over p r y h⟩, fun e ↦
    valuativePoint_ext K p (by rw [e.1, specAlgebraMap_valExt]) (by rw [e.2, valExt_over])⟩
variable (K) in

def valExtEquiv : {x : Spec (.of V) ⟶ X // x ≫ p = r} ≃
    {y : Spec (.of K) ⟶ X // y ≫ p = specAlgebraMap V K ≫ r} where
  toFun x := ⟨specAlgebraMap V K ≫ x.1, by rw [Category.assoc, x.2]⟩
  invFun y := ⟨valExt p r y.1 y.2, valExt_over ..⟩
  left_inv x := Subtype.ext
    ((eq_valExt_iff p r _ (by rw [Category.assoc, x.2]) x.1).mpr ⟨rfl, x.2⟩).symm
  right_inv y := Subtype.ext (specAlgebraMap_valExt p r y.1 y.2)
@[simp]
theorem valExtEquiv_apply_coe (x : {x : Spec (.of V) ⟶ X // x ≫ p = r}) :
    (valExtEquiv K p r x).1 = specAlgebraMap V K ≫ x.1 := rfl
@[simp]
theorem valExtEquiv_symm_apply_coe
    (y : {y : Spec (.of K) ⟶ X // y ≫ p = specAlgebraMap V K ≫ r}) :
    ((valExtEquiv K p r).symm y).1 = valExt p r y.1 y.2 := rfl
variable {V' K' : Type u} [CommRing V'] [IsDomain V'] [ValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']
def valCentre : X := valExt p r y h (closedPoint V)
end Extension
section Ring
variable {O : Type u} [CommRing O] (V : Type u) {K : Type u} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra O V] [Algebra O K]
  [IsScalarTower O V K] {X X' : Scheme.{u}}
def valExtOver (p : X ⟶ Spec (.of O)) [UniversallyClosed p] [IsSeparated p]
    (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap O K) : Spec (.of V) ⟶ X :=
  valExt p (specAlgebraMap O V) y (h.trans (specAlgebraMap_comp O V K).symm)
variable (p : X ⟶ Spec (.of O)) [UniversallyClosed p] [IsSeparated p]
  (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap O K)
@[reassoc (attr := simp)]
theorem specAlgebraMap_valExtOver : specAlgebraMap V K ≫ valExtOver V p y h = y :=
  specAlgebraMap_valExt ..
@[reassoc (attr := simp)]
theorem valExtOver_over : valExtOver V p y h ≫ p = specAlgebraMap O V :=
  valExt_over ..
end Ring
section Domination
variable {V K K' : Type*} [CommRing V] [Field K] [Field K']
theorem mem_iff_mem_range_of_isLocalHom [IsDomain V] [ValuationRing V] [Algebra V K]
    [IsFractionRing V K] (χ : K →+* K') (V' : ValuationSubring K') (ψ : V →+* V') [IsLocalHom ψ]
    (w : ∀ a, (ψ a : K') = χ (algebraMap V K a)) (x : K) :
    χ x ∈ V' ↔ x ∈ (algebraMap V K).range := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · rcases ValuationRing.isInteger_or_isInteger V x with h | ⟨a, ha⟩
    · exact h
    · obtain rfl | hx0 := eq_or_ne x 0
      · exact zero_mem _
      have hu : IsUnit (ψ a) := isUnit_iff_exists_inv.mpr ⟨⟨χ x, hx⟩, Subtype.ext (by
        simp [w, ha, hx0])⟩
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (IsUnit.of_map ψ a hu)
      refine ⟨b, ?_⟩
      have := congrArg (algebraMap V K) hb
      rw [map_mul, ha, map_one, inv_mul_eq_one₀ hx0] at this
      exact this.symm
  · rintro ⟨a, rfl⟩
    rw [← w]
    exact (ψ a).2
def comapToValuationSubring (V' : ValuationSubring K') (χ : K →+* K') : V'.comap χ →+* V' :=
  (χ.comp (V'.comap χ).subtype).codRestrict V'.toSubring fun a ↦ a.2
@[simp]
theorem coe_comapToValuationSubring (V' : ValuationSubring K') (χ : K →+* K') (a : V'.comap χ) :
    (comapToValuationSubring V' χ a : K') = χ a := rfl
instance isLocalHom_comapToValuationSubring (V' : ValuationSubring K') (χ : K →+* K') :
    IsLocalHom (comapToValuationSubring V' χ) := ⟨fun a ha ↦ by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hb' : χ a * b = 1 := congrArg Subtype.val hb
  have ha0 : (a : K) ≠ 0 := fun e ↦ by simp [e] at hb'
  have hm : (a : K)⁻¹ ∈ V'.comap χ := by
    rw [ValuationSubring.mem_comap, map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact b.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩⟩
end Domination
section Graph
variable {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {U Z Z₁ Z₂ S : Scheme.{u}}
  (p₁ : Z₁ ⟶ S) [UniversallyClosed p₁] [IsSeparated p₁]
  (p₂ : Z₂ ⟶ S) [UniversallyClosed p₂] [IsSeparated p₂]
  (j₁ : U ⟶ Z₁) (j₂ : U ⟶ Z₂) (w : j₁ ≫ p₁ = j₂ ≫ p₂)
  (r : Spec (.of V) ⟶ S) (y : Spec (.of K) ⟶ U) (h : y ≫ j₁ ≫ p₁ = specAlgebraMap V K ≫ r)
end Graph
section Centre
variable {X X' S : Scheme.{u}} [IsIntegral X] [IsIntegral X']
variable (X) in

def genericFieldPoint : Spec (.of X.functionField) ⟶ X := X.fromSpecStalk (genericPoint X)
theorem specAlgebraMap_fromSpecStalk (x : X) :
    specAlgebraMap (X.presheaf.stalk x) X.functionField ≫ X.fromSpecStalk x =
      genericFieldPoint X :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
def DominatesStalk (W : ValuationSubring X.functionField) (x : X) : Prop :=
  (∀ a : X.presheaf.stalk x, algebraMap _ X.functionField a ∈ W) ∧
    ∀ a ∈ maximalIdeal (X.presheaf.stalk x), algebraMap _ X.functionField a ∈ W.nonunits
variable {W : ValuationSubring X.functionField} {x : X}
theorem dominatesStalk_iff_exists_isLocalHom : DominatesStalk W x ↔
    ∃ ψ : X.presheaf.stalk x →+* W, IsLocalHom ψ ∧
      ∀ a, (ψ a : X.functionField) = algebraMap _ X.functionField a := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨(algebraMap _ X.functionField).codRestrict W.toSubring h₁, ⟨fun a ha ↦ ?_⟩,
      fun _ ↦ rfl⟩
    by_contra hu
    exact (W.coe_mem_nonunits_iff (a := ⟨_, h₁ a⟩)).mp (h₂ a hu) ha
  · rintro ⟨ψ, _, hψ⟩
    refine ⟨fun a ↦ hψ a ▸ (ψ a).2, fun a ha ↦ ?_⟩
    rw [← hψ, W.coe_mem_nonunits_iff]
    exact map_nonunit ψ a ha
theorem dominatesStalk_iff_range_le : DominatesStalk W x ↔
    LocalSubring.range (algebraMap (X.presheaf.stalk x) X.functionField) ≤ W.toLocalSubring := by
  have hs : IsLocalHom (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict :=
    .of_surjective _ (RingHom.rangeRestrict_surjective _)
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨by rintro _ ⟨a, rfl⟩; exact h₁ a, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ ha
    have hu : IsUnit a := by
      by_contra hu
      exact (W.coe_mem_nonunits_iff (a := ⟨_, h₁ a⟩)).mp (h₂ a hu) ha
    exact hu.map (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
  · intro h
    exact dominatesStalk_iff_exists_isLocalHom.mpr
      ⟨_, @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h.2 hs, fun _ ↦ rfl⟩
theorem exists_dominatesStalk (x : X) :
    ∃ W : ValuationSubring X.functionField, DominatesStalk W x := by
  obtain ⟨W, hW⟩ := (LocalSubring.range
    (algebraMap (X.presheaf.stalk x) X.functionField)).exists_le_valuationSubring
  exact ⟨W, dominatesStalk_iff_range_le.mpr hW⟩
theorem dominatesStalk_iff_exists_hom : DominatesStalk W x ↔
    ∃ l : Spec (.of W) ⟶ X, specAlgebraMap W X.functionField ≫ l = genericFieldPoint X ∧
      l (closedPoint W) = x := by
  rw [dominatesStalk_iff_exists_isLocalHom]
  constructor
  · rintro ⟨ψ, _, hψ⟩
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x, ?_, ?_⟩
    · rw [← specAlgebraMap_fromSpecStalk x, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
      exact RingHom.ext hψ
    · exact (congrArg (X.fromSpecStalk x) (comap_closedPoint ψ)).trans
        Scheme.fromSpecStalk_closedPoint
  · rintro ⟨l, hl, rfl⟩
    refine ⟨(Scheme.stalkClosedPointTo l).hom, inferInstance, fun a ↦ ?_⟩
    have e : Spec.map (Scheme.stalkClosedPointTo l ≫
          CommRingCat.ofHom (algebraMap W X.functionField)) ≫ X.fromSpecStalk _ =
        specAlgebraMap (X.presheaf.stalk (l (closedPoint W))) X.functionField ≫
          X.fromSpecStalk (l (closedPoint W)) := by
      rw [specAlgebraMap_fromSpecStalk, ← hl, Spec.map_comp, Category.assoc,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact congr($(Spec.map_injective ((cancel_mono _).mp e)) a)
theorem DominatesStalk.unique [X.IsSeparated] {x' : X} (h : DominatesStalk W x)
    (h' : DominatesStalk W x') : x = x' := by
  obtain ⟨l, hl, rfl⟩ := dominatesStalk_iff_exists_hom.mp h
  obtain ⟨l', hl', rfl⟩ := dominatesStalk_iff_exists_hom.mp h'
  rw [valuativePoint_ext_of_isSeparated X.functionField (hl.trans hl'.symm)]
theorem DominatesStalk.range_eq_of_valuationRing [ValuationRing (X.presheaf.stalk x)]
    (h : DominatesStalk W x) :
    (algebraMap (X.presheaf.stalk x) X.functionField).range = W.toSubring := by
  obtain ⟨ψ, _, hψ⟩ := dominatesStalk_iff_exists_isLocalHom.mp h
  ext f
  exact (mem_iff_mem_range_of_isLocalHom (RingHom.id _) W ψ hψ f).symm
section Normal
variable [IsNormalScheme X] [IsLocallyNoetherian X]
theorem DominatesStalk.range_eq (h : DominatesStalk W x) (hx : Order.coheight x = 1) :
    (algebraMap (X.presheaf.stalk x) X.functionField).range = W.toSubring :=
  have := IsNormalScheme.isDiscreteValuationRing_stalk hx
  h.range_eq_of_valuationRing
theorem DominatesStalk.exists_ringEquiv (h : DominatesStalk W x) (hx : Order.coheight x = 1) :
    ∃ e : X.presheaf.stalk x ≃+* W,
      ∀ a, (e a : X.functionField) = algebraMap _ X.functionField a := by
  obtain ⟨ψ, _, hψ⟩ := dominatesStalk_iff_exists_isLocalHom.mp h
  refine ⟨RingEquiv.ofBijective ψ ⟨fun a b e ↦ ?_, fun b ↦ ?_⟩, hψ⟩
  · apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [← hψ, ← hψ, e]
  · obtain ⟨a, ha⟩ := (h.range_eq hx).ge b.2
    exact ⟨a, Subtype.ext ((hψ a).trans ha)⟩
theorem DominatesStalk.isDiscreteValuationRing (h : DominatesStalk W x)
    (hx : Order.coheight x = 1) : IsDiscreteValuationRing W := by
  obtain ⟨e, -⟩ := h.exists_ringEquiv hx
  have := IsNormalScheme.isDiscreteValuationRing_stalk hx
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
theorem DominatesStalk.ne_top (h : DominatesStalk W x) (hx : Order.coheight x = 1) : W ≠ ⊤ := by
  have := h.isDiscreteValuationRing hx
  rintro rfl
  exact IsDiscreteValuationRing.not_isField (⊤ : ValuationSubring X.functionField)
    (MulEquiv.isField (Field.toIsField X.functionField) Subring.topEquiv.toMulEquiv)
end Normal
def functionFieldMap (f : X ⟶ X') [IsDominant f] : X'.functionField →+* X.functionField :=
  (X'.presheaf.stalkSpecializes (x := f (genericPoint X)) (y := genericPoint X') (by
    have := (genericPoint_spec X).image f.continuous
    rw [Set.image_univ, f.denseRange.closure_range] at this
    exact this.specializes trivial) ≫ f.stalkMap (genericPoint X)).hom
variable {O : Type u} [CommRing O]
def toFunctionField (p : X ⟶ Spec (.of O)) : O →+* X.functionField :=
  ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom
theorem genericFieldPoint_over (p : X ⟶ Spec (.of O)) :
    genericFieldPoint X ≫ p = Spec.map (CommRingCat.ofHom (toFunctionField p)) := by
  change X.fromSpecStalk _ ≫ p = Spec.map ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial)
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc,
    Category.assoc, ← Scheme.toSpecΓ_naturality_assoc]
  simp
theorem DominatesStalk.toFunctionField_mem (h : DominatesStalk W x) (p : X ⟶ Spec (.of O))
    (a : O) : toFunctionField p a ∈ W := by
  have := h.1 (X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of O)).inv a)))
  have _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤) (x := x) trivial _) ▸ this
variable (p : X ⟶ Spec (.of O)) [UniversallyClosed p] [IsSeparated p]
  (W : ValuationSubring X.functionField) (hW : ∀ a : O, toFunctionField p a ∈ W)
omit [UniversallyClosed p] [IsSeparated p] in
theorem genericFieldPoint_over_codRestrict : genericFieldPoint X ≫ p =
    specAlgebraMap W X.functionField ≫ Spec.map (CommRingCat.ofHom (S := W)
      ((toFunctionField p).codRestrict W.toSubring hW)) := by
  rw [genericFieldPoint_over, ← Spec.map_comp]
  rfl
def centreHom : Spec (.of W) ⟶ X :=
  valExt p _ (genericFieldPoint X) (genericFieldPoint_over_codRestrict p W hW)
@[reassoc (attr := simp)]
theorem specAlgebraMap_centreHom :
    specAlgebraMap W X.functionField ≫ centreHom p W hW = genericFieldPoint X :=
  specAlgebraMap_valExt ..
def centre : X := centreHom p W hW (closedPoint W)
theorem dominatesStalk_centre : DominatesStalk W (centre p W hW) :=
  dominatesStalk_iff_exists_hom.mpr ⟨_, specAlgebraMap_centreHom p W hW, rfl⟩
theorem centre_eq_iff (x : X) : centre p W hW = x ↔ DominatesStalk W x := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  exact ⟨fun e ↦ e ▸ dominatesStalk_centre p W hW, (dominatesStalk_centre p W hW).unique⟩
theorem exists_centre_eq (x : X) : ∃ (W : ValuationSubring X.functionField)
    (hW : ∀ a : O, toFunctionField p a ∈ W), centre p W hW = x := by
  obtain ⟨W, hW⟩ := exists_dominatesStalk x
  exact ⟨W, hW.toFunctionField_mem p, (centre_eq_iff ..).mpr hW⟩
end Centre
example : ∃ (W : ValuationSubring (Spec (.of ℤ)).functionField)
    (hW : ∀ a : ℤ, toFunctionField (𝟙 (Spec (.of ℤ))) a ∈ W),
    Order.coheight (centre (𝟙 _) W hW) = 1 ∧ IsDiscreteValuationRing W ∧ W ≠ ⊤ := by
  let x : Spec (.of ℤ) :=
    ⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two⟩
  have hx : Order.coheight x = 1 := by
    rw [← idealHeight_eq_coheight]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (R := ℤ)
      (mem_nonZeroDivisors_of_ne_zero two_ne_zero) Int.prime_two.not_unit
  obtain ⟨W, hW, e⟩ := exists_centre_eq (𝟙 (Spec (.of ℤ))) x
  have hd := (centre_eq_iff _ W hW x).mp e
  exact ⟨W, hW, e ▸ hx, hd.isDiscreteValuationRing hx, hd.ne_top hx⟩
end GlobalTheory


