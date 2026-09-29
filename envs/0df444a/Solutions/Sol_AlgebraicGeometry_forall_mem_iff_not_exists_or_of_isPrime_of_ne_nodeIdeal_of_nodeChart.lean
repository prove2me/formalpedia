-- Prove2me | solution 1 for AlgebraicGeometry.forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/19cadd4d-f141-571e-8140-85a836cdfb01

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
import Theorems.Thm_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible
import Theorems.Thm_AlgebraicCurve_NodeRingLayers_isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer
import Theorems.Thm_IsLocalRing_isDiscreteValuationRing_localization_of_ringEquiv_adicCompletion_uvCrossingModel_of_mem_of_ne
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace NRU345

section Transport

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (φ : F ≃+* X.functionField)

noncomputable def locHom (z : X) : X.presheaf.stalk z →+* F :=
  (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk z) X.functionField)

theorem locHom_apply (z : X) (s : X.presheaf.stalk z) :
    locHom φ z s = φ.symm (algebraMap (X.presheaf.stalk z) X.functionField s) := rfl

theorem φ_locHom (z : X) (s : X.presheaf.stalk z) :
    φ (locHom φ z s) = algebraMap (X.presheaf.stalk z) X.functionField s := by
  rw [locHom_apply, RingEquiv.apply_symm_apply]

theorem locHom_injective (z : X) : Function.Injective (locHom φ z) :=
  φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)

theorem range_locHom (z : X) : (locHom φ z).range = SemistableModel.localRing X φ z := rfl

theorem mem_localRing_iff (z : X) (f : F) :
    f ∈ SemistableModel.localRing X φ z ↔ ∃ s, locHom φ z s = f := Iff.rfl

theorem locHom_mem (z : X) (s : X.presheaf.stalk z) : locHom φ z s ∈ SemistableModel.localRing X φ z :=
  ⟨s, rfl⟩

noncomputable def locEquiv (z : X) : X.presheaf.stalk z ≃+* ↥(SemistableModel.localRing X φ z) :=
  RingEquiv.ofBijective (locHom φ z).rangeRestrict
    ⟨fun a b h => locHom_injective φ z (congrArg Subtype.val h), (locHom φ z).rangeRestrict_surjective⟩

@[scoped simp] theorem coe_locEquiv (z : X) (s : X.presheaf.stalk z) :
    ((locEquiv φ z s : ↥(SemistableModel.localRing X φ z)) : F) = locHom φ z s := rfl

theorem isUnit_iff_exists_mul_eq_one (z : X) (s : X.presheaf.stalk z) :
    IsUnit s ↔ ∃ g ∈ SemistableModel.localRing X φ z, locHom φ z s * g = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨locHom φ z ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), locHom_mem φ z _, ?_⟩
    rw [← map_mul, Units.mul_inv, map_one]
  · rintro ⟨g, ⟨t, rfl⟩, h⟩
    change locHom φ z s * locHom φ z t = 1 at h
    rw [← map_mul] at h
    have h1 : s * t = 1 := locHom_injective φ z (by rw [h, map_one])
    exact IsUnit.of_mul_eq_one t h1

theorem locHom_stalkSpecializes {z₁ z₂ : X} (h : z₁ ⤳ z₂) (s : X.presheaf.stalk z₂) :
    locHom φ z₁ ((X.presheaf.stalkSpecializes h).hom s) = locHom φ z₂ s := by
  simp only [locHom_apply, RingHom.algebraMap_toAlgebra]
  congr 1
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom s = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]

theorem localRing_le_of_specializes {z₁ z₂ : X} (h : z₁ ⤳ z₂) :
    SemistableModel.localRing X φ z₂ ≤ SemistableModel.localRing X φ z₁ := by
  rintro f ⟨s, rfl⟩
  exact ⟨(X.presheaf.stalkSpecializes h).hom s, locHom_stalkSpecializes φ h s⟩

noncomputable def VK (V : ValuationSubring F) : ValuationSubring X.functionField :=
  V.comap (φ.symm : X.functionField ≃+* F).toRingHom

theorem mem_VK_iff (V : ValuationSubring F) (k : X.functionField) : k ∈ VK φ V ↔ φ.symm k ∈ V := Iff.rfl

theorem algebraMap_mem_VK_iff (V : ValuationSubring F) (z : X) (s : X.presheaf.stalk z) :
    algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V ↔ locHom φ z s ∈ V := Iff.rfl

theorem mem_VK_nonunits_iff (V : ValuationSubring F) (k : X.functionField) :
    k ∈ (VK φ V).nonunits ↔ φ.symm k ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_VK_iff, map_inv₀,
    map_eq_zero_iff _ φ.symm.injective]

theorem forall_mem_VK_iff (V : ValuationSubring F) (z : X) :
    (∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V) ↔
      SemistableModel.localRing X φ z ≤ V.toSubring := by
  constructor
  · rintro h f ⟨s, rfl⟩; exact h s
  · intro h s; exact h (locHom_mem φ z s)

theorem mem_nonunits_iff_not_isUnit (V : ValuationSubring F) {f : F} (hf : f ∈ V) :
    f ∈ V.nonunits ↔ ¬ IsUnit (⟨f, hf⟩ : ↥V) := by
  have := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨f, hf⟩))
  exact this

end Transport

theorem algebraMap_germ_appTop {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    algebraMap (X.presheaf.stalk y) X.functionField
      ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
    SemistableModel.baseToFunctionField f a := by
  unfold SemistableModel.baseToFunctionField
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem isUnit_germ_appTop_iff {R : Type} [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    IsUnit ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) ↔
      a ∉ (f.base y).asIdeal := by

  have h1 : (X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
      (f.stalkMap y).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
    have h := Scheme.Hom.germ_stalkMap f ⊤ y trivial
    have h' := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
    exact h'.symm
  have h2 : ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = (StructureSheaf.toStalk R (f.base y)).hom a := by
    have h := congrArg (fun g => g.hom a) (StructureSheaf.algebraMap_germ (R := R) ⊤ (f.base y) trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [Scheme.ΓSpecIso_inv]
    exact h
  rw [h1, h2]

  have hloc : IsLocalHom (f.stalkMap y).hom :=
    Scheme.Hom.instIsLocalHomCarrierStalkCommRingCatPresheafCoeContinuousMapCarrierCarrierHomTopCatBaseRingHomHomStalkMap f y
  have h3 : IsUnit ((f.stalkMap y).hom ((StructureSheaf.toStalk R (f.base y)).hom a)) ↔
      IsUnit ((StructureSheaf.toStalk R (f.base y)).hom a) :=
    ⟨fun hu => hloc.map_nonunit _ hu, fun hu => hu.map _⟩
  rw [h3, ← StructureSheaf.stalkAlgebra_map]

  have h4 : algebraMap R ((Spec.structureSheaf R).presheaf.stalk (f.base y)) a =
      StructureSheaf.stalkIso R (f.base y) (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a) :=
    ((StructureSheaf.stalkIso R (f.base y)).commutes a).symm
  rw [h4]
  have h5 : IsUnit (StructureSheaf.stalkIso R (f.base y) (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a)) ↔
      IsUnit (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a) :=
    ⟨fun hu => by simpa using hu.map (StructureSheaf.stalkIso R (f.base y)).symm, fun hu => hu.map _⟩
  rw [h5, IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (f.base y).asIdeal) (f.base y).asIdeal]
  rfl

end NRU345
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

namespace NRU

section S0

variable {F : Type} [Field F] (T : Subring F) (𝔭 : Ideal ↥T) [𝔭.IsPrime]

theorem mem_ofPrime_iff (f : F) :
    f ∈ (LocalSubring.ofPrime T 𝔭).toSubring ↔ ∃ b c : ↥T, c ∉ 𝔭 ∧ f * (c : F) = (b : F) := by
  classical
  constructor
  · intro hf
    obtain ⟨⟨b, c⟩, h⟩ := IsLocalization.surj 𝔭.primeCompl (⟨f, hf⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring)
    refine ⟨b, (c : ↥T), c.2, ?_⟩
    have := congrArg (fun w : ↥(LocalSubring.ofPrime T 𝔭).toSubring => (w : F)) h
    simp at this
    exact this
  · rintro ⟨b, c, hc, h⟩
    have hc0 : (c : F) ≠ 0 := by
      intro h0; apply hc
      have : c = 0 := Subtype.ext h0
      rw [this]; exact zero_mem 𝔭
    have hu : IsUnit (algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring c) :=
      IsLocalization.map_units (M := 𝔭.primeCompl) _ ⟨c, hc⟩
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hwc : (w : F) = (c : F)⁻¹ := by
      have := congrArg (fun z : ↥(LocalSubring.ofPrime T 𝔭).toSubring => (z : F)) hw
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      exact (DivisionMonoid.inv_eq_of_mul _ _ this).symm
    have hf : f = (b : F) * (c : F)⁻¹ := by rw [← h, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    rw [hf, ← hwc]
    exact mul_mem (LocalSubring.le_ofPrime T 𝔭 b.2) w.2

theorem mem_maximalIdeal_ofPrime_iff (t : ↥T) :
    (⟨(t : F), LocalSubring.le_ofPrime T 𝔭 t.2⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∈
        maximalIdeal ↥(LocalSubring.ofPrime T 𝔭).toSubring ↔ t ∈ 𝔭 :=
  IsLocalization.AtPrime.to_map_mem_maximal_iff ↥(LocalSubring.ofPrime T 𝔭).toSubring 𝔭 t

theorem not_isUnit_ofPrime_iff (f : F) (b c : ↥T) (hc : c ∉ 𝔭) (hf : f * (c : F) = (b : F))
    (hfm : f ∈ (LocalSubring.ofPrime T 𝔭).toSubring) :
    ¬ IsUnit (⟨f, hfm⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ↔ b ∈ 𝔭 := by
  classical
  set Lx := (LocalSubring.ofPrime T 𝔭).toSubring with hLxdef
  have hcu : IsUnit (⟨(c : F), LocalSubring.le_ofPrime T 𝔭 c.2⟩ : ↥Lx) := by
    have := (mem_maximalIdeal_ofPrime_iff T 𝔭 c).not.2 hc
    rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at this
  have hprod : (⟨f, hfm⟩ : ↥Lx) * ⟨(c : F), LocalSubring.le_ofPrime T 𝔭 c.2⟩ =
      ⟨(b : F), LocalSubring.le_ofPrime T 𝔭 b.2⟩ := Subtype.ext hf
  rw [← mem_maximalIdeal_ofPrime_iff T 𝔭 b, mem_maximalIdeal, mem_nonunits_iff, ← hprod]
  exact ⟨fun h hu => h (isUnit_of_mul_isUnit_left hu), fun h hu => h (hu.mul hcu)⟩

end S0
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

section HT

theorem closure_le_localRing
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (N₀ T : Subring F)
    (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (η : X) (hN : N₀ ≤ SemistableModel.localRing X φ η) :
    T ≤ SemistableModel.localRing X φ η := by
  rw [hT]
  refine Subring.closure_le.2 (Set.union_subset hN ?_)
  rintro f ⟨a, rfl⟩

  refine ⟨(X.presheaf.germ ⊤ η trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)), ?_⟩
  change φ.symm (algebraMap _ _ ((X.presheaf.germ ⊤ η trivial).hom
    (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) = algebraMap L F (a : L)
  have h1 : algebraMap (X.presheaf.stalk η) X.functionField
      ((X.presheaf.germ ⊤ η trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
      SemistableModel.baseToFunctionField toBase a := by
    unfold SemistableModel.baseToFunctionField
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
  rw [h1, ← hφ, RingEquiv.symm_apply_apply]

end HT
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

namespace NRU

theorem not_isUnit_const_of_mem_maximalIdeal
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (η : X) (hη : toBase.base η = IsLocalRing.closedPoint ↥A) (a : ↥A) (ha : a ∈ IsLocalRing.maximalIdeal ↥A)
    (hmem : algebraMap L F (a : L) ∈ SemistableModel.localRing X φ η) :
    ¬ IsUnit (⟨algebraMap L F (a : L), hmem⟩ : ↥(SemistableModel.localRing X φ η)) := by
  intro hu
  set s : X.presheaf.stalk η :=
    (X.presheaf.germ ⊤ η trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) with hsdef
  have hs : NRU345.locHom φ η s = algebraMap L F (a : L) := by
    rw [NRU345.locHom_apply, hsdef, NRU345.algebraMap_germ_appTop toBase η a, ← hφ, RingEquiv.symm_apply_apply]
  have hsu : ¬ IsUnit s := by
    rw [hsdef, NRU345.isUnit_germ_appTop_iff toBase η a, hη]
    exact fun h => h ha
  apply hsu
  have heq : NRU345.locEquiv φ η s = ⟨algebraMap L F (a : L), hmem⟩ :=
    Subtype.ext (by rw [NRU345.coe_locEquiv, hs])
  rw [← heq] at hu
  simpa using hu.map (NRU345.locEquiv φ η).symm.toRingHom

theorem exists_frac_of_mem_ofPrime
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A)
    (N₀ : Subring F)
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (𝔭 : Ideal ↥T) [𝔭.IsPrime]
    (Bx : Subring F) (hBxN₀ : ∀ f : F, f ∈ Bx → f ∈ N₀)
    (hN₀Bx : ∀ f : F, f ∈ N₀ ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ N₀, IsUnit (⟨h, hh⟩ : ↥N₀)) ∧ f * h = g)
    (T₀ : Finset F)
    (hT₀ : Bx = Subring.closure ({f : F | ∃ c : L, c ∈ C' ∧ f = algebraMap L F c} ∪ (↑T₀ : Set F)))
    (B : Subring F) (hB : B = Subring.closure (Set.range (fun a : ↥A => algebraMap L F (a : L)) ∪ (↑T₀ : Set F))) :
    ∃ hBLx : B ≤ (LocalSubring.ofPrime T 𝔭).toSubring,
      ∀ f : F, f ∈ (LocalSubring.ofPrime T 𝔭).toSubring →
        ∃ b c : F, b ∈ B ∧ ∃ hc : c ∈ B,
          (⟨c, hBLx hc⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∉
              IsLocalRing.maximalIdeal ↥(LocalSubring.ofPrime T 𝔭).toSubring ∧ f * c = b := by
  classical

  have hAT : ∀ a : ↥A, algebraMap L F (a : L) ∈ T := fun a => by
    rw [hT]; exact Subring.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)
  have hN₀T : ∀ f : F, f ∈ N₀ → f ∈ T := fun f hf => by
    rw [hT]; exact Subring.subset_closure (Set.mem_union_left _ hf)
  have hT₀Bx : (↑T₀ : Set F) ⊆ Bx := fun f hf => by
    rw [hT₀]; exact Subring.subset_closure (Set.mem_union_right _ hf)
  have hBxB : Bx ≤ B := by
    rw [hT₀, hB]
    apply Subring.closure_mono
    rintro f (⟨c, hc, rfl⟩ | hf)
    · exact Set.mem_union_left _ ⟨⟨c, hC'A c hc⟩, rfl⟩
    · exact Set.mem_union_right _ hf
  have hBT : B ≤ T := by
    rw [hB]
    refine (Subring.closure_le (t := T)).2 ?_
    rintro f (⟨a, rfl⟩ | hf)
    · exact hAT a
    · exact hN₀T f (hBxN₀ f (hT₀Bx hf))
  have hTLx : T ≤ (LocalSubring.ofPrime T 𝔭).toSubring := LocalSubring.le_ofPrime T 𝔭
  refine ⟨hBT.trans hTLx, ?_⟩

  have key : ∀ t : F, t ∈ T → ∃ b h : F, b ∈ B ∧ h ∈ B ∧ ∃ hh : h ∈ N₀, IsUnit (⟨h, hh⟩ : ↥N₀) ∧ t * h = b := by
    intro t ht
    rw [hT] at ht
    induction ht using Subring.closure_induction with
    | mem f hf =>
      rcases hf with hf | ⟨a, rfl⟩
      · obtain ⟨g, h, hg, hh, hu, hfh⟩ := (hN₀Bx f).1 hf
        exact ⟨g, h, hBxB hg, hBxB hh, hBxN₀ h hh, hu (hBxN₀ h hh), hfh⟩
      · refine ⟨algebraMap L F (a : L), 1, ?_, B.one_mem, N₀.one_mem, isUnit_one, mul_one _⟩
        rw [hB]; exact Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
    | zero => exact ⟨0, 1, B.zero_mem, B.one_mem, N₀.one_mem, isUnit_one, by rw [zero_mul]⟩
    | one => exact ⟨1, 1, B.one_mem, B.one_mem, N₀.one_mem, isUnit_one, by rw [one_mul]⟩
    | add f g _ _ ihf ihg =>
      obtain ⟨b₁, h₁, hb₁, hh₁, hh₁N, hu₁, e₁⟩ := ihf
      obtain ⟨b₂, h₂, hb₂, hh₂, hh₂N, hu₂, e₂⟩ := ihg
      refine ⟨b₁ * h₂ + b₂ * h₁, h₁ * h₂, B.add_mem (B.mul_mem hb₁ hh₂) (B.mul_mem hb₂ hh₁), B.mul_mem hh₁ hh₂,
        N₀.mul_mem hh₁N hh₂N, ?_, ?_⟩
      · have : (⟨h₁ * h₂, N₀.mul_mem hh₁N hh₂N⟩ : ↥N₀) = ⟨h₁, hh₁N⟩ * ⟨h₂, hh₂N⟩ := rfl
        rw [this]; exact hu₁.mul hu₂
      · rw [← e₁, ← e₂]; ring
    | neg f _ ihf =>
      obtain ⟨b, h, hb, hh, hhN, hu, e⟩ := ihf
      exact ⟨-b, h, B.neg_mem hb, hh, hhN, hu, by rw [← e]; ring⟩
    | mul f g _ _ ihf ihg =>
      obtain ⟨b₁, h₁, hb₁, hh₁, hh₁N, hu₁, e₁⟩ := ihf
      obtain ⟨b₂, h₂, hb₂, hh₂, hh₂N, hu₂, e₂⟩ := ihg
      refine ⟨b₁ * b₂, h₁ * h₂, B.mul_mem hb₁ hb₂, B.mul_mem hh₁ hh₂, N₀.mul_mem hh₁N hh₂N, ?_, ?_⟩
      · have : (⟨h₁ * h₂, N₀.mul_mem hh₁N hh₂N⟩ : ↥N₀) = ⟨h₁, hh₁N⟩ * ⟨h₂, hh₂N⟩ := rfl
        rw [this]; exact hu₁.mul hu₂
      · rw [← e₁, ← e₂]; ring

  have hunitN₀ : ∀ (h : F) (hh : h ∈ N₀), IsUnit (⟨h, hh⟩ : ↥N₀) → ∀ hh' : h ∈ (LocalSubring.ofPrime T 𝔭).toSubring,
      IsUnit (⟨h, hh'⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) := by
    intro h hh hu hh'
    let ι : ↥N₀ →+* ↥(LocalSubring.ofPrime T 𝔭).toSubring :=
      Subring.inclusion (fun f hf => hTLx (hN₀T f hf))
    have : ι ⟨h, hh⟩ = ⟨h, hh'⟩ := rfl
    rw [← this]; exact hu.map ι

  intro f hf
  obtain ⟨⟨t₁, ⟨t₂, ht₂⟩⟩, e⟩ :=
    IsLocalization.surj 𝔭.primeCompl (⟨f, hf⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring)
  have e' : f * (t₂ : F) = (t₁ : F) := by
    have := congrArg Subtype.val e
    simp at this
    exact this
  obtain ⟨b₁, h₁, hb₁, hh₁, hh₁N, hu₁, e₁⟩ := key _ t₁.2
  obtain ⟨b₂, h₂, hb₂, hh₂, hh₂N, hu₂, e₂⟩ := key _ t₂.2
  refine ⟨b₁ * h₂, b₂ * h₁, B.mul_mem hb₁ hh₂, B.mul_mem hb₂ hh₁, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have ht₂u : IsUnit (algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring t₂) :=
      IsLocalization.map_units _ (⟨t₂, ht₂⟩ : 𝔭.primeCompl)
    have hval : (⟨b₂ * h₁, (hBT.trans hTLx) (B.mul_mem hb₂ hh₁)⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) =
        algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring t₂ *
          ⟨h₂, hTLx (hN₀T _ hh₂N)⟩ * ⟨h₁, hTLx (hN₀T _ hh₁N)⟩ := by
      apply Subtype.ext
      change b₂ * h₁ = (t₂ : F) * h₂ * h₁
      rw [← e₂]
    rw [hval]
    exact (ht₂u.mul (hunitN₀ h₂ hh₂N hu₂ _)).mul (hunitN₀ h₁ hh₁N hu₁ _)
  · calc f * (b₂ * h₁) = f * ((t₂ : F) * h₂ * h₁) := by rw [← e₂]
      _ = (f * (t₂ : F)) * h₁ * h₂ := by ring
      _ = (t₁ : F) * h₁ * h₂ := by rw [e']
      _ = b₁ * h₂ := by rw [e₁]

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

open IsLocalRing

namespace NRU

section Generic

variable {L : Type} [Field L] {A : ValuationSubring L} {F : Type} [Field F] [Algebra L F] {N₀ : Subring F}

def IsNA (N₀ : Subring F) (A : ValuationSubring L) (x : F) : Prop :=
  ∃ l : List (↥N₀ × ↥A), x = (l.map fun p => (p.1 : F) * algebraMap L F (p.2 : L)).sum

def IsBad (N₀ : Subring F) (A : ValuationSubring L) (x : F) : Prop :=
  ∃ l : List (↥N₀ × ↥A), (∀ p ∈ l, ¬ IsUnit p.1 ∨ p.2 ∈ maximalIdeal ↥A) ∧
    x = (l.map fun p => (p.1 : F) * algebraMap L F (p.2 : L)).sum

theorem isBad_zero : IsBad N₀ A 0 := ⟨[], by simp, by simp⟩

theorem IsBad.add {x y : F} (hx : IsBad N₀ A x) (hy : IsBad N₀ A y) : IsBad N₀ A (x + y) := by
  obtain ⟨l₁, h₁, rfl⟩ := hx
  obtain ⟨l₂, h₂, rfl⟩ := hy
  refine ⟨l₁ ++ l₂, fun p hp => ?_, by simp⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem IsBad.mul_left (n : ↥N₀) (a : ↥A) {x : F} (hx : IsBad N₀ A x) :
    IsBad N₀ A ((n : F) * algebraMap L F (a : L) * x) := by
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l.map fun p => (n * p.1, a * p.2), fun p hp => ?_, ?_⟩
  · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    rcases hl p' hp' with h | h
    · left; exact fun hu => h (isUnit_of_mul_isUnit_right hu)
    · right; exact Ideal.mul_mem_left _ _ h
  · clear hl
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]
      push_cast
      ring

end Generic
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

variable {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
  (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
  (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
  (N₀ : Subring F) [IsLocalRing ↥N₀]
  (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
  (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
  (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
    ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
  (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
  (𝔭 : Ideal ↥T)
  (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
    {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))

omit hC'A hϖ' hC'N₀ hconst hlin h𝔭 in
include hT in
theorem isNA_of_mem (x : F) (hx : x ∈ T) : IsNA N₀ A x := by
  subst hT

  have hmul : ∀ y ∈ Submonoid.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))),
      ∃ (n : ↥N₀) (a : ↥A), y = (n : F) * algebraMap L F (a : L) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
      rcases hz with hz | ⟨a, rfl⟩
      · exact ⟨⟨z, hz⟩, 1, by simp⟩
      · exact ⟨1, a, by simp⟩
    | one => exact ⟨1, 1, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨n, a, rfl⟩ := hy
      obtain ⟨n', a', rfl⟩ := hz
      refine ⟨n * n', a * a', ?_⟩
      push_cast
      ring
  have hneg : ∀ l : List (↥N₀ × ↥A), -(l.map fun p => (p.1 : F) * algebraMap L F (p.2 : L)).sum =
      ((l.map fun p => (-p.1, p.2)).map fun p => (p.1 : F) * algebraMap L F (p.2 : L)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, neg_add, ih]
      push_cast; ring
  rw [Subring.mem_closure_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨n, a, rfl⟩ := hmul z hz
    exact ⟨[(n, a)], by simp⟩
  | zero => exact ⟨[], by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l₁, rfl⟩ := hy
    obtain ⟨l₂, rfl⟩ := hz
    exact ⟨l₁ ++ l₂, by simp⟩
  | neg y _ hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l.map fun p => (-p.1, p.2), hneg l⟩

omit hC'A hϖ' hC'N₀ hconst hlin h𝔭 in
include hT in
theorem IsBad.mul_mem {t x : F} (ht : t ∈ T) (hx : IsBad N₀ A x) : IsBad N₀ A (t * x) := by
  obtain ⟨l, rfl⟩ := isNA_of_mem A N₀ T hT t ht
  clear ht
  induction l with
  | nil => simpa using (isBad_zero : IsBad N₀ A 0)
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact (hx.mul_left p.1 p.2).add ih

omit hC'A hϖ' hC'N₀ hconst hlin in
include hT h𝔭 in
theorem isBad_of_mem {p : ↥T} (hp : p ∈ 𝔭) : IsBad N₀ A (p : F) := by
  subst h𝔭
  induction hp using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨f, hf, hx⟩ | ⟨a, ha, hx⟩
    · exact ⟨[(f, 1)], fun p hp => by simp at hp; subst hp; exact Or.inl hf, by simp [hx]⟩
    · exact ⟨[(1, a)], fun p hp => by simp at hp; subst hp; exact Or.inr ha, by simp [hx]⟩
  | zero => simpa using (isBad_zero : IsBad N₀ A 0)
  | add x y _ _ hx hy => simpa using hx.add hy
  | smul t x _ hx =>
    show IsBad N₀ A (((t * x : ↥T)) : F)
    push_cast
    exact IsBad.mul_mem A N₀ T hT t.2 hx

def toA : ↥C' →+* ↥A where
  toFun d := ⟨(d : L), hC'A d d.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

omit hϖ' in
@[scoped simp] theorem toA_coe (d : ↥C') : ((toA A C' hC'A d : ↥A) : L) = (d : L) := rfl

def toN : ↥C' →+* ↥N₀ where
  toFun d := ⟨algebraMap L F (d : L), hC'N₀ d d.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem toN_coe (d : ↥C') : ((toN C' N₀ hC'N₀ d : ↥N₀) : F) = algebraMap L F (d : L) := rfl

include hϖ' in

theorem residue_toA_eq_zero (hϖ'0 : ϖ' ≠ 0) (d : ↥C') (hd : ¬ IsUnit d) : residue ↥A (toA A C' hC'A d) = 0 := by
  classical
  set ρ : ↥C' →+* ResidueField ↥A := (residue ↥A).comp (toA A C' hC'A) with hρ
  have hρ' : ∀ x : ↥C', ρ x = 0 ↔ ∃ d' : ↥C', x = ϖ' * d' := fun x => hϖ' x
  have hϖ'nu : ¬ IsUnit ϖ' := fun hu => by
    have h : ρ 1 = 0 := (hρ' 1).mpr ⟨↑hu.unit⁻¹, hu.mul_val_inv.symm⟩
    exact one_ne_zero ((map_one ρ).symm.trans h)
  show ρ d = 0
  by_cases hd0 : d = 0
  · rw [hd0, map_zero]
  obtain ⟨ϖ₀, hirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥C'
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
  obtain ⟨k', u', hk'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ'0 hirr
  have hk'pos : k' ≠ 0 := by
    rintro rfl; apply hϖ'nu; rw [hk', pow_zero, mul_one]; exact Units.isUnit u'
  have hkpos : k ≠ 0 := by
    rintro rfl; apply hd; rw [hk, pow_zero, mul_one]; exact Units.isUnit u
  have hρϖ₀ : ρ ϖ₀ = 0 := by
    have h : ρ ϖ' = 0 := (hρ' ϖ').mpr ⟨1, by simp⟩
    rw [hk', map_mul, map_pow] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h ((Units.isUnit u').map ρ).ne_zero
    · exact pow_eq_zero_iff hk'pos |>.mp h
  rw [hk, map_mul, map_pow, hρϖ₀, zero_pow hkpos, mul_zero]

include hC'A hϖ' hC'N₀ hconst hlin in

theorem not_isBad_one (hϖ'0 : ϖ' ≠ 0) : ¬ IsBad N₀ A (1 : F) := by
  classical
  rintro ⟨l, hl, h1⟩

  set m := l.length with hm
  set nn : Fin m → ↥N₀ := fun i => (l.get i).1 with hnn
  set aa : Fin m → ↥A := fun i => (l.get i).2 with haa
  have hbad : ∀ i, ¬ IsUnit (nn i) ∨ aa i ∈ maximalIdeal ↥A := fun i => hl _ (List.get_mem l i)
  have h1' : (1 : F) = ∑ i : Fin m, (nn i : F) * algebraMap L F (aa i : L) := by
    rw [h1, ← List.sum_ofFn]
    congr 1
    apply List.ext_getElem (by simp [hm])
    intro i h₁ h₂
    simp [hnn, haa]
  clear h1 hl

  let Asub : Submodule ↥C' L :=
    { carrier := A
      add_mem' := fun hx hy => A.add_mem _ _ hx hy
      zero_mem' := A.zero_mem
      smul_mem' := fun c x hx => by
        show (c : L) * x ∈ A
        exact A.mul_mem _ _ (hC'A c c.2) hx }
  let S : Set L := insert 1 (Set.range fun i : Fin m => ((aa i : ↥A) : L))
  have hSfin : S.Finite := (Set.finite_range _).insert 1
  let M : Submodule ↥C' L := Submodule.span ↥C' S
  have hMA : M ≤ Asub := by
    rw [Submodule.span_le]
    rintro x (rfl | ⟨i, rfl⟩)
    · exact A.one_mem
    · exact (aa i).2
  haveI : Module.Finite ↥C' ↥M := Module.Finite.iff_fg.mpr (Submodule.fg_span hSfin)
  haveI : NoZeroSMulDivisors ↥C' ↥M := by
    refine ⟨fun {c x} h => ?_⟩
    have : (c : L) * (x : L) = 0 := by
      have := congrArg Subtype.val h
      simpa [Submodule.coe_smul] using this
    rcases mul_eq_zero.mp this with h | h
    · left; exact Subtype.ext (by simpa using h)
    · right; exact Subtype.ext (by simpa using h)
  haveI : Module.Free ↥C' ↥M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ↥C' ↥M
  let b₀ := Module.Free.chooseBasis ↥C' ↥M
  haveI : Fintype ι := inferInstance
  set n := Fintype.card ι with hn
  let b : Module.Basis (Fin n) ↥C' ↥M := b₀.reindex (Fintype.equivFin ι)
  let e : Fin n → L := fun s => ((b s : ↥M) : L)
  have hli : LinearIndependent ↥C' e := b.linearIndependent.map' M.subtype M.ker_subtype
  have heA : ∀ s, e s ∈ A := fun s => hMA (b s).2

  have hrepr : ∀ (y : L) (hy : y ∈ M), y = ∑ s, ((b.repr ⟨y, hy⟩ s : ↥C') : L) * e s := by
    intro y hy
    have := congrArg (fun z : ↥M => (z : L)) (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm.trans (Finset.sum_congr rfl fun s _ => rfl)
  have h1M : (1 : L) ∈ M := Submodule.subset_span (Set.mem_insert _ _)
  have haM : ∀ i, ((aa i : ↥A) : L) ∈ M := fun i => Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  set r1 : Fin n → ↥C' := fun s => b.repr ⟨1, h1M⟩ s with hr1
  set ra : Fin m → Fin n → ↥C' := fun i s => b.repr ⟨_, haM i⟩ s with hra
  have h1e : (1 : L) = ∑ s, (r1 s : L) * e s := hrepr 1 h1M
  have hae : ∀ i, ((aa i : ↥A) : L) = ∑ s, (ra i s : L) * e s := fun i => hrepr _ (haM i)

  set ψ := toN C' N₀ hC'N₀ with hψ
  set ν : Fin n → ↥N₀ := fun s => (∑ i, nn i * ψ (ra i s)) - ψ (r1 s) with hν
  have hrel : ∑ s, e s • ((ν s : ↥N₀) : F) = 0 := by
    simp only [hν, Algebra.smul_def]
    push_cast
    have : ∀ i : Fin m, algebraMap L F ((aa i : ↥A) : L) = ∑ s, algebraMap L F (ra i s : L) * algebraMap L F (e s) := by
      intro i; rw [hae i, map_sum]; simp only [map_mul]
    have h1F : (1 : F) = ∑ s, algebraMap L F (r1 s : L) * algebraMap L F (e s) := by
      conv_lhs => rw [← map_one (algebraMap L F), h1e, map_sum]
      simp only [map_mul]

    calc ∑ s, algebraMap L F (e s) * (∑ i, (nn i : F) * algebraMap L F (ra i s : L) - algebraMap L F (r1 s : L))
        = ∑ i, (nn i : F) * (∑ s, algebraMap L F (ra i s : L) * algebraMap L F (e s)) -
            ∑ s, algebraMap L F (r1 s : L) * algebraMap L F (e s) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1
          · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun s _ => by ring))
          · exact Finset.sum_congr rfl (fun s _ => by ring)
      _ = 0 := by
          rw [← h1F, sub_eq_zero, h1']
          exact Finset.sum_congr rfl (fun i _ => by rw [this i])
  have hν0 : ∀ s, ν s = 0 := hlin n e ν hli hrel

  choose o ho hou using hconst
  have hoN : ∀ g : ↥N₀, residue ↥N₀ g = residue ↥N₀ (ψ (o g)) := by
    intro g
    apply Ideal.Quotient.eq.mpr
    exact (mem_maximalIdeal _).mpr (hou g)
  set δ : Fin n → ↥C' := fun s => r1 s - ∑ i, o (nn i) * ra i s with hδ
  have hδnu : ∀ s, ¬ IsUnit (δ s) := by
    intro s hu
    have h0 : residue ↥N₀ (ψ (δ s)) = 0 := by
      have := congrArg (residue ↥N₀) (hν0 s)
      rw [map_zero] at this
      rw [← neg_eq_zero, ← this]
      simp only [hν, hδ, map_sub, map_sum, map_mul, neg_sub]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by rw [hoN (nn i)])
    exact (residue_ne_zero_iff_isUnit _).mpr (hu.map ψ) h0
  have honu : ∀ i, ¬ IsUnit (nn i) → ¬ IsUnit (o (nn i)) := by
    intro i hni hu
    have h1 : residue ↥N₀ (nn i) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hni)
    rw [hoN (nn i)] at h1
    exact (residue_ne_zero_iff_isUnit _).mpr (hu.map ψ) h1

  have hsum : ∑ s, (δ s : L) * e s = 1 - ∑ i, ((o (nn i) : ↥C') : L) * ((aa i : ↥A) : L) := by
    have : ∀ s, (δ s : L) = (r1 s : L) - ∑ i, ((o (nn i) : ↥C') : L) * (ra i s : L) := by
      intro s; simp only [hδ]; push_cast; rfl
    simp only [this, sub_mul, Finset.sum_sub_distrib, ← h1e]
    congr 1
    simp only [hae, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun s _ => by ring))
  have hL : (1 : L) = ∑ s, (δ s : L) * e s + ∑ i, ((o (nn i) : ↥C') : L) * ((aa i : ↥A) : L) := by
    rw [hsum]; ring
  have hA1 : (1 : ↥A) = ∑ s, toA A C' hC'A (δ s) * ⟨e s, heA s⟩ + ∑ i, toA A C' hC'A (o (nn i)) * aa i := by
    apply Subtype.ext
    rw [show (((∑ s, toA A C' hC'A (δ s) * ⟨e s, heA s⟩ + ∑ i, toA A C' hC'A (o (nn i)) * aa i : ↥A)) : L) =
      A.subtype (∑ s, toA A C' hC'A (δ s) * ⟨e s, heA s⟩ + ∑ i, toA A C' hC'A (o (nn i)) * aa i) from rfl]
    rw [map_add, map_sum, map_sum]
    simp only [map_mul]
    exact hL
  have hres := congrArg (residue ↥A) hA1
  rw [map_one, map_add, map_sum, map_sum] at hres
  have hz1 : ∀ s, residue ↥A (toA A C' hC'A (δ s) * ⟨e s, heA s⟩) = 0 := fun s => by
    rw [map_mul, residue_toA_eq_zero A C' hC'A ϖ' hϖ' hϖ'0 (δ s) (hδnu s), zero_mul]
  have hz2 : ∀ i, residue ↥A (toA A C' hC'A (o (nn i)) * aa i) = 0 := fun i => by
    rw [map_mul]
    rcases hbad i with h | h
    · rw [residue_toA_eq_zero A C' hC'A ϖ' hϖ' hϖ'0 _ (honu i h), zero_mul]
    · rw [(residue_eq_zero_iff _).mpr h, mul_zero]
  simp only [hz1, hz2, Finset.sum_const_zero, add_zero] at hres
  exact one_ne_zero hres

include hT in
omit hC'A hϖ' hC'N₀ hconst hlin h𝔭 in
theorem coe_N₀_mem_T (n : ↥N₀) : (n : F) ∈ T := by
  rw [hT]; exact Subring.subset_closure (Or.inl n.2)

include hT in
omit hC'A hϖ' hC'N₀ hconst hlin h𝔭 in
theorem algebraMap_mem_T (a : ↥A) : algebraMap L F (a : L) ∈ T := by
  rw [hT]; exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)

include hT h𝔭 in
omit hC'A hϖ' hC'N₀ hconst hlin in
theorem mem_p_of_not_isUnit (m : ↥N₀) (hm : ¬ IsUnit m) :
    (⟨(m : F), coe_N₀_mem_T A N₀ T hT m⟩ : ↥T) ∈ 𝔭 := by
  rw [h𝔭]; exact Ideal.subset_span (Or.inl ⟨m, hm, rfl⟩)

include hT h𝔭 in
omit hC'A hϖ' hC'N₀ hconst hlin in
theorem mem_p_of_mem_maximalIdeal (a : ↥A) (ha : a ∈ maximalIdeal ↥A) :
    (⟨algebraMap L F (a : L), algebraMap_mem_T A N₀ T hT a⟩ : ↥T) ∈ 𝔭 := by
  rw [h𝔭]; exact Ideal.subset_span (Or.inr ⟨a, ha, rfl⟩)

include hC'A hC'N₀ hconst hT h𝔭 in
omit hϖ' hlin in

theorem exists_const_add_mem (t : ↥T) :
    ∃ (a : ↥A) (p : ↥T), p ∈ 𝔭 ∧ (t : F) = algebraMap L F (a : L) + (p : F) := by
  classical
  obtain ⟨l, hl⟩ := isNA_of_mem A N₀ T hT (t : F) t.2
  rw [hl]
  clear hl
  induction l with
  | nil => exact ⟨0, 0, 𝔭.zero_mem, by simp⟩
  | cons q l ih =>
    obtain ⟨a, p, hp, h⟩ := ih
    obtain ⟨o, ho, hou⟩ := hconst q.1

    have hmT : ((q.1 - ⟨_, ho⟩ : ↥N₀) : F) * algebraMap L F (q.2 : L) ∈ T :=
      T.mul_mem (coe_N₀_mem_T A N₀ T hT _) (algebraMap_mem_T A N₀ T hT q.2)
    have hm𝔭 : (⟨_, hmT⟩ : ↥T) ∈ 𝔭 := by
      have : (⟨_, hmT⟩ : ↥T) = ⟨_, coe_N₀_mem_T A N₀ T hT (q.1 - ⟨_, ho⟩)⟩ * ⟨_, algebraMap_mem_T A N₀ T hT q.2⟩ :=
        Subtype.ext rfl
      rw [this]
      exact Ideal.mul_mem_right _ _ (mem_p_of_not_isUnit A N₀ T hT 𝔭 h𝔭 _ hou)
    refine ⟨toA A C' hC'A o * q.2 + a, ⟨_, hmT⟩ + p, 𝔭.add_mem hm𝔭 hp, ?_⟩
    simp only [List.map_cons, List.sum_cons, h]
    push_cast
    simp only [toA_coe, map_mul]
    ring

include hC'A hϖ' hC'N₀ hconst hlin hT h𝔭 in

theorem isMaximal_p (hϖ'0 : ϖ' ≠ 0) : 𝔭.IsMaximal := by
  classical
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => not_isBad_one A C' hC'A ϖ' hϖ' N₀ hC'N₀ hconst hlin hϖ'0 ?_, ?_⟩
  · simpa using isBad_of_mem A N₀ T hT 𝔭 h𝔭 h1
  · intro J x hJ hx hxJ
    obtain ⟨a, p, hp, hxp⟩ := exists_const_add_mem A C' hC'A N₀ hC'N₀ hconst T hT 𝔭 h𝔭 x
    have ha : a ∉ maximalIdeal ↥A := by
      intro ha
      apply hx
      have : x = ⟨_, algebraMap_mem_T A N₀ T hT a⟩ + p := Subtype.ext (by simpa using hxp)
      rw [this]
      exact 𝔭.add_mem (mem_p_of_mem_maximalIdeal A N₀ T hT 𝔭 h𝔭 a ha) hp
    have hau : IsUnit a := by rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at ha
    obtain ⟨ainv, hainv⟩ := hau.exists_right_inv

    have : (1 : ↥T) = ⟨_, algebraMap_mem_T A N₀ T hT ainv⟩ * (x - p) := by
      apply Subtype.ext
      push_cast
      rw [hxp, add_sub_cancel_right, ← map_mul]
      have : ((ainv : ↥A) : L) * (a : L) = 1 := by
        have := congrArg (fun z : ↥A => (z : L)) hainv; simpa [mul_comm] using this
      rw [this, map_one]
    rw [this]
    exact J.mul_mem_left _ (J.sub_mem hxJ (hJ hp))

section GoingUp

omit hC'A hϖ' hC'N₀ hconst hlin hT h𝔭 in

theorem exists_dvd_all {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → R) : ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with hs' | hs'
    · subst hs'; exact ⟨i, Finset.mem_insert_self _ _, fun j hj => by simp at hj; subst hj; exact dvd_rfl⟩
    obtain ⟨i₀, hi₀, hdiv⟩ := ih hs'
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (f i) (f i₀)
    ·
      refine ⟨i, Finset.mem_insert_self _ _, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact dvd_rfl
      · exact (Dvd.intro c hc).trans (hdiv j hj)
    · refine ⟨i₀, Finset.mem_insert_of_mem hi₀, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Dvd.intro c hc
      · exact hdiv j hj

omit hϖ' hC'N₀ hconst hlin hT h𝔭 in

theorem exists_aeval_eq_zero_coeff_eq_one (a : L) (ha : IsAlgebraic ↥C' a) :
    ∃ g : Polynomial ↥C', Polynomial.aeval a g = 0 ∧ ∃ i, g.coeff i = 1 := by
  classical
  obtain ⟨f, hf0, hfa⟩ := ha
  have hsupp : f.support.Nonempty := Polynomial.nonempty_support_iff.mpr hf0
  obtain ⟨i₀, hi₀, hdiv⟩ := exists_dvd_all f.support hsupp (fun j => f.coeff j)
  have hc0 : f.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hdvd : ∀ j, f.coeff i₀ ∣ f.coeff j := fun j => by
    by_cases hj : j ∈ f.support
    · exact hdiv j hj
    · rw [Polynomial.notMem_support_iff.mp hj]; exact dvd_zero _
  choose qq hqq using hdvd
  let g : Polynomial ↥C' := ∑ j ∈ f.support, Polynomial.C (qq j) * Polynomial.X ^ j
  have hfg : f = Polynomial.C (f.coeff i₀) * g := by
    conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
    simp only [g, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_assoc, ← Polynomial.C_mul, ← hqq j]
  refine ⟨g, ?_, i₀, ?_⟩
  · have := hfa
    rw [hfg, map_mul, Polynomial.aeval_C, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ↥C' L)).mp h) hc0
    · exact h
  · have : g.coeff i₀ = qq i₀ := by
      simp only [g, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq, if_pos hi₀]
    rw [this]
    have h : f.coeff i₀ * qq i₀ = f.coeff i₀ * 1 := by rw [mul_one]; exact (hqq i₀).symm
    exact mul_left_cancel₀ hc0 h

variable (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)

include hC'A hϖ' hC'N₀ hconst hlin hT h𝔭 halg in

theorem le_p_of_isPrime (hϖ'0 : ϖ' ≠ 0) (𝔮 : Ideal ↥T) [h𝔮p : 𝔮.IsPrime]
    (h𝔮 : ∀ a : ↥A, a ∈ maximalIdeal ↥A → (⟨algebraMap L F (a : L), algebraMap_mem_T A N₀ T hT a⟩ : ↥T) ∈ 𝔮) :
    𝔮 ≤ 𝔭 := by
  classical
  have h𝔭max := isMaximal_p A C' hC'A ϖ' hϖ' N₀ hC'N₀ hconst hlin T hT 𝔭 h𝔭 hϖ'0

  let I : Ideal ↥T := Ideal.span {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}
  have hI𝔮 : I ≤ 𝔮 := by
    rw [Ideal.span_le]; rintro t ⟨a, ha, ht⟩
    have : t = ⟨_, algebraMap_mem_T A N₀ T hT a⟩ := Subtype.ext ht
    rw [this]; exact h𝔮 a ha
  have hNT : N₀ ≤ T := fun x hx => coe_N₀_mem_T A N₀ T hT ⟨x, hx⟩
  let ψT : ↥N₀ →+* ↥T := Subring.inclusion hNT
  let π : ↥T →+* (↥T ⧸ I) := Ideal.Quotient.mk I
  letI alg : Algebra ↥N₀ (↥T ⧸ I) := (π.comp ψT).toAlgebra
  have halgmap : ∀ n : ↥N₀, algebraMap ↥N₀ (↥T ⧸ I) n = π (ψT n) := fun _ => rfl
  let θ : ↥C' →+* ↥T := ψT.comp (toN C' N₀ hC'N₀)
  have hθ : ∀ d : ↥C', (θ d : F) = algebraMap L F (d : L) := fun _ => rfl
  let ρC : ↥C' →+* (↥T ⧸ I) := π.comp θ
  have hρC : ∀ d ∈ maximalIdeal ↥C', ρC d = 0 := by
    intro d hd
    show π (θ d) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    refine Ideal.subset_span ⟨toA A C' hC'A d, ?_, rfl⟩
    exact (residue_eq_zero_iff _).mp
      (residue_toA_eq_zero A C' hC'A ϖ' hϖ' hϖ'0 d ((mem_maximalIdeal _).mp hd))
  let κ : ResidueField ↥C' →+* (↥T ⧸ I) := Ideal.Quotient.lift (maximalIdeal ↥C') ρC hρC
  have hκ : κ.comp (residue ↥C') = ρC := RingHom.ext (fun d => by
    show κ (Ideal.Quotient.mk _ d) = ρC d
    exact Ideal.Quotient.lift_mk _ _ _)
  letI algκ : Algebra (ResidueField ↥C') (↥T ⧸ I) := κ.toAlgebra

  have hint : ∀ a : ↥A, IsIntegral ↥N₀ (π ⟨algebraMap L F (a : L), algebraMap_mem_T A N₀ T hT a⟩) := by
    intro a
    set ā := π ⟨algebraMap L F (a : L), algebraMap_mem_T A N₀ T hT a⟩ with hā
    obtain ⟨g, hga, i, hgi⟩ := exists_aeval_eq_zero_coeff_eq_one C' (a : L) (halg a a.2)

    have hgT : Polynomial.eval₂ θ ⟨algebraMap L F (a : L), algebraMap_mem_T A N₀ T hT a⟩ g = 0 := by
      apply Subtype.ext
      show T.subtype (Polynomial.eval₂ θ _ g) = 0
      rw [Polynomial.hom_eval₂]
      have h1 : T.subtype.comp θ = (algebraMap L F).comp (algebraMap ↥C' L) := RingHom.ext (fun d => rfl)
      rw [h1, show T.subtype ⟨algebraMap L F (a : L), algebraMap_mem_T A N₀ T hT a⟩ = algebraMap L F (a : L) from rfl,
        ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hga, map_zero]
    have hgbar : Polynomial.eval₂ ρC ā g = 0 := by
      rw [hā, show ρC = π.comp θ from rfl, ← Polynomial.hom_eval₂, hgT, map_zero]
    have hgbar0 : g.map (residue ↥C') ≠ 0 := fun h => by
      have := congrArg (fun p : Polynomial (ResidueField ↥C') => p.coeff i) h
      simp only [Polynomial.coeff_map, hgi, map_one, Polynomial.coeff_zero] at this
      exact one_ne_zero this
    have halgk : IsAlgebraic (ResidueField ↥C') ā := by
      refine ⟨g.map (residue ↥C'), hgbar0, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, show algebraMap (ResidueField ↥C') (↥T ⧸ I) = κ from rfl, hκ]
      exact hgbar
    obtain ⟨p, hpm, hp0⟩ := halgk.isIntegral

    have hlifts : p ∈ Polynomial.lifts (residue ↥C') := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact residue_surjective _
    obtain ⟨q, hqp, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hpm
    refine ⟨q.map (toN C' N₀ hC'N₀), hqm.map _, ?_⟩
    rw [Polynomial.eval₂_map, show (algebraMap ↥N₀ (↥T ⧸ I)).comp (toN C' N₀ hC'N₀) = ρC from rfl, ← hκ,
      ← Polynomial.eval₂_map, hqp]
    exact hp0

  haveI hInt : Algebra.IsIntegral ↥N₀ (↥T ⧸ I) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨l, hl⟩ := isNA_of_mem A N₀ T hT (t : F) t.2
    have ht : t = (l.map fun p => ψT p.1 * ⟨algebraMap L F (p.2 : L), algebraMap_mem_T A N₀ T hT p.2⟩).sum := by
      apply Subtype.ext
      rw [hl]
      show _ = T.subtype _
      rw [map_list_sum, List.map_map]
      rfl
    rw [ht, show Ideal.Quotient.mk I _ = π _ from rfl, map_list_sum, List.map_map]
    clear hl ht
    induction l with
    | nil => simpa using isIntegral_zero
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons]
      refine IsIntegral.add ?_ ih
      show IsIntegral ↥N₀ (π (ψT p.1 * _))
      rw [map_mul, ← halgmap]
      exact (isIntegral_algebraMap).mul (hint p.2)

  have hker : RingHom.ker π ≤ 𝔮 := by rw [show π = Ideal.Quotient.mk I from rfl, Ideal.mk_ker]; exact hI𝔮
  haveI : (𝔮.map π).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : (𝔮.map π).comap (algebraMap ↥N₀ (↥T ⧸ I)) ≤ maximalIdeal ↥N₀ := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    apply (Ideal.IsPrime.ne_top ‹(𝔮.map π).IsPrime›)
    rw [Ideal.eq_top_iff_one] at htop ⊢
    simpa using htop
  obtain ⟨Q, hQ𝔮, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (maximalIdeal ↥N₀) (𝔮.map π) hcomap
  have h𝔭Q : 𝔭 ≤ Q.comap π := by
    rw [h𝔭, Ideal.span_le]
    rintro t (⟨m, hm, ht⟩ | ⟨a, ha, ht⟩)
    · have : t = ψT m := Subtype.ext ht
      show π t ∈ Q
      rw [this, ← halgmap, ← Ideal.mem_comap, hQcomap]
      exact (mem_maximalIdeal _).mpr hm
    · show π t ∈ Q
      have : π t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a, ha, ht⟩)
      rw [this]; exact Q.zero_mem
  have hQ' : Q.comap π = 𝔭 := (h𝔭max.eq_of_le (Ideal.comap_ne_top π hQprime.ne_top) h𝔭Q).symm
  calc 𝔮 ≤ (𝔮.map π).comap π := Ideal.le_comap_map
    _ ≤ Q.comap π := Ideal.comap_mono hQ𝔮
    _ = 𝔭 := hQ'

end GoingUp
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345"

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

namespace NRU
namespace Layers

variable {L : Type} [Field L] {F : Type} [Field F] [Algebra L F]

def CS (A : ValuationSubring L) (C' : Subring L) (S : Finset L) : Subring L :=
  A.toSubring ⊓ (Subfield.closure ((C' : Set L) ∪ (↑S : Set L))).toSubring

theorem mem_CS_iff (A : ValuationSubring L) (C' : Subring L) (S : Finset L) (c : L) :
    c ∈ CS A C' S ↔ c ∈ A ∧ c ∈ Subfield.closure ((C' : Set L) ∪ (↑S : Set L)) := by
  simp [CS, Subring.mem_inf]

theorem CS_mono (A : ValuationSubring L) (C' : Subring L) {S S' : Finset L} (h : S ⊆ S') :
    CS A C' S ≤ CS A C' S' := by
  intro c hc
  rw [mem_CS_iff] at hc ⊢
  exact ⟨hc.1, Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.mpr h)) hc.2⟩

theorem le_CS (A : ValuationSubring L) (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) (S : Finset L) :
    C' ≤ CS A C' S := fun c hc =>
  (mem_CS_iff A C' S c).mpr ⟨hC'A c hc, Subfield.subset_closure (Set.mem_union_left _ hc)⟩

theorem mem_CS_of_mem (A : ValuationSubring L) (C' : Subring L) (S : Finset L) (hS : ∀ s ∈ S, s ∈ A)
    {s : L} (hs : s ∈ S) : s ∈ CS A C' S :=
  (mem_CS_iff A C' S s).mpr ⟨hS s hs, Subfield.subset_closure (Set.mem_union_right _ (Finset.mem_coe.mpr hs))⟩

def TS (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L) (S : Finset L) : Subring F :=
  Subring.closure ((N₀ : Set F) ∪ {f : F | ∃ c : L, c ∈ CS A C' S ∧ f = algebraMap L F c})

theorem TS_def (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L) (S : Finset L) :
    TS N₀ A C' S = Subring.closure ((N₀ : Set F) ∪ {f : F | ∃ c : L, c ∈ CS A C' S ∧ f = algebraMap L F c}) := rfl

theorem le_TS (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L) (S : Finset L) : N₀ ≤ TS N₀ A C' S :=
  fun f hf => Subring.subset_closure (Set.mem_union_left _ hf)

theorem algebraMap_mem_TS (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L) (S : Finset L) {c : L}
    (hc : c ∈ CS A C' S) : algebraMap L F c ∈ TS N₀ A C' S :=
  Subring.subset_closure (Set.mem_union_right _ ⟨c, hc, rfl⟩)

theorem TS_mono (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L) {S S' : Finset L} (h : S ⊆ S') :
    TS N₀ A C' S ≤ TS N₀ A C' S' := by
  apply Subring.closure_mono
  rintro f (hf | ⟨c, hc, rfl⟩)
  · exact Set.mem_union_left _ hf
  · exact Set.mem_union_right _ ⟨c, CS_mono A C' h hc, rfl⟩

theorem TS_le (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L) (S : Finset L)
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L)))) :
    TS N₀ A C' S ≤ T := by
  rw [hT]
  apply Subring.closure_mono
  rintro f (hf | ⟨c, hc, rfl⟩)
  · exact Set.mem_union_left _ hf
  · exact Set.mem_union_right _ ⟨⟨c, ((mem_CS_iff A C' S c).mp hc).1⟩, rfl⟩

theorem exists_finset_mem_TS (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L)
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    {t : F} (ht : t ∈ T) :
    ∃ S : Finset L, (∀ s ∈ S, s ∈ A) ∧ t ∈ TS N₀ A C' S := by
  classical
  rw [hT] at ht
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨a, rfl⟩
    · exact ⟨∅, by simp, le_TS _ _ _ _ hx⟩
    · refine ⟨{(a : L)}, by simp, algebraMap_mem_TS _ _ _ _ ?_⟩
      exact mem_CS_of_mem A C' _ (by simp) (Finset.mem_singleton_self _)
  | zero => exact ⟨∅, by simp, zero_mem _⟩
  | one => exact ⟨∅, by simp, one_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, hS₁, hx⟩ := hx
    obtain ⟨S₂, hS₂, hy⟩ := hy
    refine ⟨S₁ ∪ S₂, fun s hs => ?_, add_mem (TS_mono _ _ _ Finset.subset_union_left hx) (TS_mono _ _ _ Finset.subset_union_right hy)⟩
    rcases Finset.mem_union.mp hs with h | h
    exacts [hS₁ s h, hS₂ s h]
  | neg x _ hx =>
    obtain ⟨S₁, hS₁, hx⟩ := hx
    exact ⟨S₁, hS₁, neg_mem hx⟩
  | mul x y _ _ hx hy =>
    obtain ⟨S₁, hS₁, hx⟩ := hx
    obtain ⟨S₂, hS₂, hy⟩ := hy
    refine ⟨S₁ ∪ S₂, fun s hs => ?_, mul_mem (TS_mono _ _ _ Finset.subset_union_left hx) (TS_mono _ _ _ Finset.subset_union_right hy)⟩
    rcases Finset.mem_union.mp hs with h | h
    exacts [hS₁ s h, hS₂ s h]

theorem mem_Lx_iff_exists_layer (N₀ : Subring F) (A : ValuationSubring L) (C' : Subring L)
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (𝔭 : Ideal ↥T)
    (Lx : Subring F) (hLx : ∀ f : F, f ∈ Lx ↔ ∃ b c : ↥T, c ∉ 𝔭 ∧ f * (c : F) = (b : F))
    (f : F) :
    f ∈ Lx ↔ ∃ (S : Finset L), (∀ s ∈ S, s ∈ A) ∧ ∃ (a b : F) (ha : a ∈ TS N₀ A C' S) (hb : b ∈ TS N₀ A C' S),
      (⟨b, TS_le N₀ A C' S T hT hb⟩ : ↥T) ∉ 𝔭 ∧ f * b = a := by
  classical
  constructor
  · intro hf
    obtain ⟨b, c, hc, hfc⟩ := (hLx f).mp hf
    obtain ⟨S₁, hS₁, hb⟩ := exists_finset_mem_TS N₀ A C' T hT b.2
    obtain ⟨S₂, hS₂, hc'⟩ := exists_finset_mem_TS N₀ A C' T hT c.2
    refine ⟨S₁ ∪ S₂, fun s hs => ?_, (b : F), (c : F), TS_mono _ _ _ Finset.subset_union_left hb,
      TS_mono _ _ _ Finset.subset_union_right hc', ?_, hfc⟩
    · rcases Finset.mem_union.mp hs with h | h
      exacts [hS₁ s h, hS₂ s h]
    · convert hc
  · rintro ⟨S, -, a, b, ha, hb, hb𝔭, hfb⟩
    exact (hLx f).mpr ⟨⟨a, TS_le N₀ A C' S T hT ha⟩, ⟨b, TS_le N₀ A C' S T hT hb⟩, hb𝔭, hfb⟩

end NRU.Layers
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace NRU
namespace Layers

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem exists_layer
    {L : Type} [Field L] [CharZero L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]

    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (hϖ'irr : Irreducible ϖ')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)

    (N₀ : Subring F) [IsLocalRing ↥N₀] [IsNoetherianRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (hdim : 2 ≤ ringKrullDim ↥N₀)

    (Wc : Type) [CommRing Wc] [IsDomain Wc] [IsDiscreteValuationRing Wc] [IsAdicComplete (maximalIdeal Wc) Wc]
    (πW : Wc) (hirr : Irreducible πW) (E : ℕ) (hE : 1 ≤ E)
    (σ : Wc →+* AdicCompletion (maximalIdeal ↥N₀) ↥N₀)
    (ιc : AdicCompletion (maximalIdeal ↥N₀) ↥N₀ ≃+* UVCrossingModel Wc (πW ^ E))
    (hσπ : ∀ h : algebraMap L F ((ϖ' : ↥C') : L) ∈ N₀,
      σ πW = algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀) ⟨_, h⟩)
    (hισ : ∀ o : Wc, ιc (σ o) = const (πW ^ E) o)
    (hσC : ∀ (c : ↥C') (h : algebraMap L F (c : L) ∈ N₀),
      ∃ o : Wc, σ o = algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀) ⟨_, h⟩)

    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (hfrac : ∀ f : F, ∃ b c : ↥T, (c : F) ≠ 0 ∧ f * (c : F) = (b : F))
    (𝔭 : Ideal ↥T)
    (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))

    (Lx : Subring F) (hLx : ∀ f : F, f ∈ Lx ↔ ∃ b c : ↥T, c ∉ 𝔭 ∧ f * (c : F) = (b : F))
    (S : Finset F) (hS : ∀ f ∈ S, f ∈ Lx) :
    ∃ (R : Subring F) (_ : IsNoetherianRing ↥R) (_ : IsLocalRing ↥R) (hNR : N₀ ≤ R) (hRL : R ≤ Lx)
      (c : ↥A) (hc : algebraMap L F (c : L) ∈ R)
      (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W)
      (π : W) (w : ℕ) (ι : AdicCompletion (maximalIdeal ↥R) ↥R ≃+* UVCrossingModel W (π ^ w)),
      (∀ f ∈ S, f ∈ R) ∧
      (∀ f : ↥N₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion hNR f)) ∧
      c ∈ maximalIdeal ↥A ∧ Irreducible π ∧ 1 ≤ w ∧
      ι (algebraMap ↥R _ ⟨algebraMap L F (c : L), hc⟩) = const (π ^ w) π ∧
      IsIntegrallyClosed ↥R ∧
      (∀ (Q : Ideal ↥R) [Q.IsPrime], (⟨algebraMap L F (c : L), hc⟩ : ↥R) ∈ Q → Q ≠ maximalIdeal ↥R →
        IsDiscreteValuationRing (Localization.AtPrime Q)) := by
  classical

  have h𝔭1 : (1 : ↥T) ∉ 𝔭 := by
    obtain ⟨b, c₀, hc₀, -⟩ := (hLx 1).mp (one_mem Lx)
    intro h1; exact hc₀ (by simpa using Ideal.mul_mem_left 𝔭 c₀ h1)
  have hAT : ∀ a : ↥A, algebraMap L F (a : L) ∈ T := by
    rw [hT]; exact fun a => Subring.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)
  have hN₀T : N₀ ≤ T := by
    rw [hT]; exact fun f hf => Subring.subset_closure (Set.mem_union_left _ hf)

  have hϖ'N₀ : ¬ IsUnit (⟨algebraMap L F ((ϖ' : ↥C') : L), hC'N₀ _ ϖ'.2⟩ : ↥N₀) := by
    intro hu
    let ψ₀ : MvPowerSeries (Fin 2) Wc →+* Wc ⧸ Ideal.span {πW} :=
      (Ideal.Quotient.mk (Ideal.span {πW})).comp (MvPowerSeries.constantCoeff (σ := Fin 2) (R := Wc))
    have hψ₀ : ∀ a ∈ uvCrossingIdeal Wc (πW ^ E), ψ₀ a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      apply mul_eq_zero_of_right
      have hcc : MvPowerSeries.constantCoeff ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Wc) * MvPowerSeries.X 1 -
          MvPowerSeries.C (πW ^ E)) = -(πW ^ E) := by
        rw [map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul, zero_sub]
      show Ideal.Quotient.mk (Ideal.span {πW}) (MvPowerSeries.constantCoeff _) = 0
      rw [hcc, map_neg, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self πW (by omega)))
    let ψ : UVCrossingModel Wc (πW ^ E) →+* Wc ⧸ Ideal.span {πW} := Ideal.Quotient.lift _ ψ₀ hψ₀
    have h1 : ψ (const (πW ^ E) πW) = 0 := by
      show Ideal.Quotient.lift _ ψ₀ hψ₀ (Ideal.Quotient.mk _ (MvPowerSeries.C πW)) = 0
      rw [Ideal.Quotient.lift_mk]
      simp only [ψ₀, RingHom.comp_apply, MvPowerSeries.constantCoeff_C]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self πW)
    have h2 : IsUnit (const (πW ^ E) πW) := by
      have h := (hu.map (algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀))).map ιc
      rwa [← hσπ (hC'N₀ _ ϖ'.2), hισ] at h
    have h3 := h2.map ψ
    rw [h1, isUnit_zero_iff] at h3
    exact hirr.not_isUnit (Ideal.span_singleton_eq_top.mp ((Ideal.Quotient.zero_eq_one_iff).mp h3))

  have hSw : ∀ f ∈ S, ∃ (Sf : Finset L), (∀ s ∈ Sf, s ∈ A) ∧ ∃ (a b : F) (ha : a ∈ TS N₀ A C' Sf) (hb : b ∈ TS N₀ A C' Sf),
      (⟨b, TS_le N₀ A C' Sf T hT hb⟩ : ↥T) ∉ 𝔭 ∧ f * b = a :=
    fun f hf => (mem_Lx_iff_exists_layer N₀ A C' T hT 𝔭 Lx hLx f).mp (hS f hf)
  choose Sf hSfA using hSw
  let Sstar : Finset L := S.attach.biUnion (fun f => Sf f.1 f.2)
  have hSstarA : ∀ s ∈ Sstar, s ∈ A := by
    intro s hs
    obtain ⟨f, -, hsf⟩ := Finset.mem_biUnion.mp hs
    exact (hSfA f.1 f.2).1 s hsf
  have hSfle : ∀ f (hf : f ∈ S), Sf f hf ⊆ Sstar := fun f hf =>
    Finset.subset_biUnion_of_mem (fun g : {x // x ∈ S} => Sf g.1 g.2) (Finset.mem_attach S ⟨f, hf⟩)

  obtain ⟨C'', instD, instDVR, ϖ'', e, R, hC'C'', hC'R, hC''A, hSC'', hC''iff, hϖ''irr, hres'', he, hϖe, hRC'', hRfin, hloc⟩ :=
    ValuationSubring.exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible A C' hC'A ϖ' hϖ'irr hϖ' halg Sstar hSstarA
  haveI := instD
  haveI := instDVR
  have hCS : CS A C' Sstar = C'' := by
    ext c; rw [mem_CS_iff, hC''iff]

  set T'' : Subring F := TS N₀ A C' Sstar with hT''def
  have hT'' : T'' = Subring.closure ((N₀ : Set F) ∪ {f : F | ∃ c : L, c ∈ C'' ∧ f = algebraMap L F c}) := by
    rw [hT''def, TS_def, hCS]
  set 𝔐 : Ideal ↥T'' := Ideal.span ({t : ↥T'' | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T'' | (t : F) = algebraMap L F ((ϖ'' : ↥C'') : L)}) with h𝔐
  obtain ⟨h𝔐max, TL, hTL, instN, instL, hle, hlocal, hresTL, hgen, hdimTL⟩ :=
    AlgebraicCurve.NodeRingLayers.isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer
      C' ϖ' hϖ'irr N₀ hC'N₀ hconst hlin hϖ'N₀ hdim C'' hC'C'' ϖ'' hϖ''irr e he hϖe R hC'R hRC'' hRfin hloc T'' hT'' 𝔐 h𝔐
  haveI := instN
  haveI := instL

  have hT''T : T'' ≤ T := TS_le N₀ A C' Sstar T hT
  have hϖ''m : (⟨((ϖ'' : ↥C'') : L), hC''A _ ϖ''.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff]; exact (hres'' ϖ'').mpr ⟨1, (mul_one _).symm⟩
  have h𝔐𝔭 : 𝔐 ≤ 𝔭.comap (Subring.inclusion hT''T) := by
    rw [h𝔐, Ideal.span_le]
    rintro t (⟨f, hf, htf⟩ | ht)
    · show Subring.inclusion hT''T t ∈ 𝔭
      rw [h𝔭]; apply Ideal.subset_span; left; exact ⟨f, hf, htf⟩
    · show Subring.inclusion hT''T t ∈ 𝔭
      rw [h𝔭]; apply Ideal.subset_span; right
      exact ⟨⟨_, hC''A _ ϖ''.2⟩, hϖ''m, ht⟩
  have h𝔐eq : 𝔐 = 𝔭.comap (Subring.inclusion hT''T) := by
    refine h𝔐max.eq_of_le ?_ h𝔐𝔭
    intro htop
    exact h𝔭1 (by simpa using (Ideal.eq_top_iff_one _).mp htop)
  have hTLLx : TL ≤ Lx := by
    intro f hf
    obtain ⟨a, b, hb, hfb⟩ := (hTL f).mp hf
    refine (hLx f).mpr ⟨⟨a, hT''T a.2⟩, ⟨b, hT''T b.2⟩, ?_, hfb⟩
    intro hb'
    exact hb (h𝔐eq ▸ hb')
  have hST : ∀ f ∈ S, f ∈ TL := by
    intro f hf
    obtain ⟨a, b, ha, hb, hb𝔭, hfb⟩ := (hSfA f hf).2
    have ha' : a ∈ T'' := TS_mono N₀ A C' (hSfle f hf) ha
    have hb' : b ∈ T'' := TS_mono N₀ A C' (hSfle f hf) hb
    refine (hTL f).mpr ⟨⟨a, ha'⟩, ⟨b, hb'⟩, ?_, hfb⟩
    intro hb𝔐
    exact hb𝔭 (by have := h𝔐𝔭 hb𝔐; (simp at this; exact this))

  obtain ⟨instWd, instWdvr, instWc, hπirr, hjinj, hjsur⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete (↥C'') ϖ'' hϖ''irr
  haveI := instWd
  haveI := instWdvr
  haveI := instWc

  haveI : IsLocalHom (Subring.inclusion hle) := ⟨fun a ha => by by_contra hna; exact hlocal a hna ha⟩
  have hconstTL : ∀ c : ↥C'', algebraMap L F (c : L) ∈ TL := by
    intro c
    have hcT'' : algebraMap L F (c : L) ∈ T'' := by
      rw [hT'']; exact Subring.subset_closure (Set.mem_union_right _ ⟨c, c.2, rfl⟩)
    refine (hTL _).mpr ⟨⟨_, hcT''⟩, 1, fun h1 => h𝔐max.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
  let c' : ↥C'' →+* ↥TL := ((algebraMap L F).comp C''.subtype).codRestrict TL (fun c => hconstTL c)
  have hc' : ∀ c : ↥C'', (c' c : F) = algebraMap L F (c : L) := fun _ => rfl
  have hϖeTL : ∃ v : ↥TL, IsUnit v ∧ Subring.inclusion hle ⟨algebraMap L F ((ϖ' : ↥C') : L), hC'N₀ _ ϖ'.2⟩ = v * c' ϖ'' ^ e := by
    obtain ⟨v, hv, hvinv, hvϖ⟩ := hϖe
    refine ⟨⟨algebraMap L F v, hconstTL ⟨v, hv⟩⟩, ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap L F v⁻¹, hconstTL ⟨v⁻¹, hvinv⟩⟩, Subtype.ext ?_⟩
      have hv0 : v ≠ 0 := by
        rintro rfl; rw [zero_mul] at hvϖ
        exact hϖ'irr.ne_zero (by exact_mod_cast hvϖ)
      show algebraMap L F v * algebraMap L F v⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hv0, map_one]
    · apply Subtype.ext
      show algebraMap L F ((ϖ' : ↥C') : L) = algebraMap L F v * (algebraMap L F ((ϖ'' : ↥C'') : L)) ^ e
      rw [hvϖ, map_mul, map_pow]
  have hresTL' : ∀ g : ↥TL, ∃ o : ↥C'', ¬ IsUnit (g - c' o) := fun g => by
    obtain ⟨o, h, hh⟩ := hresTL g; exact ⟨o, hh⟩
  have hgen' : maximalIdeal ↥TL ≤ (maximalIdeal ↥N₀).map (Subring.inclusion hle) ⊔ Ideal.span {c' ϖ''} :=
    hgen (hconstTL ϖ'')
  obtain ⟨σ', ι', hσ', hι'⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer
      πW hirr σ ⟨algebraMap L F ((ϖ' : ↥C') : L), hC'N₀ _ ϖ'.2⟩ (hσπ (hC'N₀ _ ϖ'.2)) E hE ιc hισ
      (Subring.inclusion hle) c' ϖ'' e hϖeTL hresTL' hgen' hdimTL
      (algebraMap ↥C'' (AdicCompletion (maximalIdeal ↥C'') ↥C'') ϖ'') hπirr
      (algebraMap ↥C'' (AdicCompletion (maximalIdeal ↥C'') ↥C'')) rfl hjinj hjsur

  have hw : 1 ≤ e * E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcTL : algebraMap L F ((⟨((ϖ'' : ↥C'') : L), hC''A _ ϖ''.2⟩ : ↥A) : L) ∈ TL := hconstTL ϖ''
  have hιc : ι' (algebraMap ↥TL _ ⟨algebraMap L F ((⟨((ϖ'' : ↥C'') : L), hC''A _ ϖ''.2⟩ : ↥A) : L), hcTL⟩) =
      const ((algebraMap ↥C'' (AdicCompletion (maximalIdeal ↥C'') ↥C'') ϖ'') ^ (e * E))
        (algebraMap ↥C'' (AdicCompletion (maximalIdeal ↥C'') ↥C'') ϖ'') := by
    have hcc : (⟨algebraMap L F ((⟨((ϖ'' : ↥C'') : L), hC''A _ ϖ''.2⟩ : ↥A) : L), hcTL⟩ : ↥TL) = c' ϖ'' := Subtype.ext rfl
    rw [hcc, ← hσ', hι']
  have hIC : IsIntegrallyClosed ↥TL :=
    IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel _ hπirr (e * E) hw ι'
  refine ⟨TL, instN, instL, hle, hTLLx, ⟨((ϖ'' : ↥C'') : L), hC''A _ ϖ''.2⟩, hcTL,
    AdicCompletion (maximalIdeal ↥C'') ↥C'', inferInstance, instWd, instWdvr, instWc,
    algebraMap ↥C'' _ ϖ'', e * E, ι', hST, hlocal, hϖ''m, hπirr, hw, hιc, hIC, ?_⟩
  intro Q hQ hcQ hQne
  exact IsLocalRing.isDiscreteValuationRing_localization_of_ringEquiv_adicCompletion_uvCrossingModel_of_mem_of_ne
    _ hπirr (e * E) hw ι' _ hιc Q hcQ hQne

end NRU.Layers
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

namespace NRU

theorem isUnit_of_isUnit_subring {L : Type} [Field L] (A : ValuationSubring L)
    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) (u : ↥C') (hu : IsUnit u) :
    IsUnit (⟨(u : L), hC'A u u.2⟩ : ↥A) := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨⟨⟨(w : ↥C'), hC'A _ (w : ↥C').2⟩, ⟨((w⁻¹ : (↥C')ˣ) : ↥C'), hC'A _ ((w⁻¹ : (↥C')ˣ) : ↥C').2⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext; show ((w : ↥C') : L) * ((w⁻¹ : (↥C')ˣ) : ↥C') = 1
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  · apply Subtype.ext; show (((w⁻¹ : (↥C')ˣ) : ↥C') : L) * (w : ↥C') = 1
    rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one]

theorem irreducible_of_residue_iff_of_pow_mem
    {L : Type} [Field L] (A : ValuationSubring L)
    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (ϖ₀ : L) (hϖ₀C : ϖ₀ ∈ C') (hϖ₀ : ϖ₀ ≠ 0) (E₀ : ℕ)
    (hmod : ∃ h : ϖ₀ ^ E₀ ∈ A, (⟨ϖ₀ ^ E₀, h⟩ : ↥A) ∈ maximalIdeal ↥A) :
    Irreducible ϖ' := by
  classical

  have hres : ∀ d : ↥C', (⟨(d : L), hC'A d d.2⟩ : ↥A) ∈ maximalIdeal ↥A ↔ ∃ d' : ↥C', d = ϖ' * d' := by
    intro d; rw [← hϖ', IsLocalRing.residue_eq_zero_iff]

  have hne : ϖ' ≠ 0 := by
    obtain ⟨h, hm⟩ := hmod
    have hd : (⟨(( ⟨ϖ₀ ^ E₀, Subring.pow_mem C' hϖ₀C E₀⟩ : ↥C') : L), hC'A _ (Subring.pow_mem C' hϖ₀C E₀)⟩ : ↥A) ∈
        maximalIdeal ↥A := by
      convert hm using 1
    obtain ⟨d', hd'⟩ := (hres _).mp hd
    intro h0
    rw [h0, zero_mul] at hd'
    have : (ϖ₀ ^ E₀ : L) = 0 := by
      have := congrArg (fun z : ↥C' => (z : L)) hd'
      simpa using this
    exact pow_ne_zero E₀ hϖ₀ this

  have hϖ'm : (⟨((ϖ' : ↥C') : L), hC'A _ ϖ'.2⟩ : ↥A) ∈ maximalIdeal ↥A := (hres ϖ').mpr ⟨1, (mul_one _).symm⟩
  have hnu : ¬ IsUnit ϖ' := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hϖ'm |>.elim (isUnit_of_isUnit_subring A C' hC'A ϖ' hu)

  obtain ⟨ϖ₁, hϖ₁⟩ := IsDiscreteValuationRing.exists_irreducible ↥C'
  obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ₁
  have hm : m ≠ 0 := by
    rintro rfl; apply hnu; rw [hu', pow_zero, mul_one]; exact Units.isUnit u'
  have hϖ₁m : (⟨((ϖ₁ : ↥C') : L), hC'A _ ϖ₁.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
    have h1 : (⟨(((u' : ↥C') * ϖ₁ ^ m : ↥C') : L), hC'A _ ((u' : ↥C') * ϖ₁ ^ m).2⟩ : ↥A) ∈ maximalIdeal ↥A := by
      convert hϖ'm using 2; rw [hu']
    have h2 : (⟨(((u' : ↥C') * ϖ₁ ^ m : ↥C') : L), hC'A _ ((u' : ↥C') * ϖ₁ ^ m).2⟩ : ↥A) =
        (⟨((u' : ↥C') : L), hC'A _ (u' : ↥C').2⟩ : ↥A) * (⟨((ϖ₁ : ↥C') : L), hC'A _ ϖ₁.2⟩ : ↥A) ^ m := by
      apply Subtype.ext; simp
    rw [h2] at h1
    have h3 := ((Ideal.IsPrime.mem_or_mem inferInstance h1).resolve_left
      (fun h => (IsLocalRing.mem_maximalIdeal _).mp h (isUnit_of_isUnit_subring A C' hC'A _ (Units.isUnit u'))))
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance m h3

  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  apply le_antisymm
  · intro d hd
    rw [Ideal.mem_span_singleton']
    rcases eq_or_ne d 0 with rfl | hd0
    · exact ⟨0, by simp⟩
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ₁
    have hn : n ≠ 0 := by
      rintro rfl; rw [pow_zero, mul_one] at hw
      exact (IsLocalRing.mem_maximalIdeal _).mp hd (hw ▸ Units.isUnit w)
    have hdm : (⟨(d : L), hC'A d d.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
      have : (⟨(d : L), hC'A d d.2⟩ : ↥A) =
          (⟨((w : ↥C') : L), hC'A _ (w : ↥C').2⟩ : ↥A) * (⟨((ϖ₁ : ↥C') : L), hC'A _ ϖ₁.2⟩ : ↥A) ^ n := by
        apply Subtype.ext; simp [hw]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖ₁m n (Nat.pos_of_ne_zero hn))
    obtain ⟨d', hd'⟩ := (hres d).mp hdm
    exact ⟨d', by rw [hd', mul_comm]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

namespace NRU

theorem two_le_ringKrullDim_of_branches
    {F : Type} [Field F] (N₀ Oi Oj : Subring F) [IsLocalRing ↥N₀] [IsLocalRing ↥Oi] [IsLocalRing ↥Oj]
    (hNi : N₀ ≤ Oi) (hNj : N₀ ≤ Oj)
    (xN yN : F) (hxN : xN ∈ N₀) (hyN : yN ∈ N₀)
    (hx_nu : ¬ ∃ g ∈ Oi, xN * g = 1) (hx_u : ∃ g ∈ Oj, xN * g = 1)
    (hy_nu : ¬ ∃ g ∈ Oj, yN * g = 1) (hy_u : ∃ g ∈ Oi, yN * g = 1) :
    2 ≤ ringKrullDim ↥N₀ := by
  classical

  have unit_iff : ∀ (O : Subring F) (z : F) (hz : z ∈ O), IsUnit (⟨z, hz⟩ : ↥O) ↔ ∃ g ∈ O, z * g = 1 := by
    intro O z hz
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨((w⁻¹ : (↥O)ˣ) : ↥O), ((w⁻¹ : (↥O)ˣ) : ↥O).2, ?_⟩
      have := congrArg (fun t : ↥O => (t : F)) w.mul_inv
      simpa [hw] using this
    · rintro ⟨g, hg, hzg⟩
      exact ⟨⟨⟨z, hz⟩, ⟨g, hg⟩, Subtype.ext hzg, Subtype.ext (by rw [mul_comm] at hzg; exact hzg)⟩, rfl⟩
  let P : Ideal ↥N₀ := (maximalIdeal ↥Oi).comap (Subring.inclusion hNi)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hxP : (⟨xN, hxN⟩ : ↥N₀) ∈ P := by
    show Subring.inclusion hNi ⟨xN, hxN⟩ ∈ maximalIdeal ↥Oi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hx_nu ((unit_iff Oi xN (hNi hxN)).mp hu)
  have hx0 : (⟨xN, hxN⟩ : ↥N₀) ≠ 0 := by
    obtain ⟨g, -, hg⟩ := hx_u
    intro h0
    have : xN = 0 := congrArg (fun t : ↥N₀ => (t : F)) h0
    rw [this, zero_mul] at hg
    exact zero_ne_one hg
  have hyP : (⟨yN, hyN⟩ : ↥N₀) ∉ P := by
    show Subring.inclusion hNi ⟨yN, hyN⟩ ∉ maximalIdeal ↥Oi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact (unit_iff Oi yN (hNi hyN)).mpr hy_u
  have hym : (⟨yN, hyN⟩ : ↥N₀) ∈ maximalIdeal ↥N₀ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨g, hg, hyg⟩ := (unit_iff N₀ yN hyN).mp hu
    exact hy_nu ⟨g, hNj hg, hyg⟩

  have h01 : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum ↥N₀) < ⟨P, hP⟩ := by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    refine bot_lt_iff_ne_bot.mpr (fun h => hx0 ?_)
    have : (⟨xN, hxN⟩ : ↥N₀) ∈ (⊥ : Ideal ↥N₀) := by
      have h' : P = ⊥ := h
      exact h' ▸ hxP
    simpa using this
  have h12 : (⟨P, hP⟩ : PrimeSpectrum ↥N₀) < ⟨maximalIdeal ↥N₀, (maximalIdeal.isMaximal ↥N₀).isPrime⟩ := by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) ?_
    intro hPm
    have : (⟨yN, hyN⟩ : ↥N₀) ∈ P := by
      have h' : P = maximalIdeal ↥N₀ := hPm
      rw [h']; exact hym
    exact hyP this
  have hh : (2 : ℕ∞) ≤ Order.height (⟨maximalIdeal ↥N₀, (maximalIdeal.isMaximal ↥N₀).isPrime⟩ : PrimeSpectrum ↥N₀) := by
    have h1 : 1 < Order.height (⟨maximalIdeal ↥N₀, (maximalIdeal.isMaximal ↥N₀).isPrime⟩ : PrimeSpectrum ↥N₀) :=
      Order.one_lt_height_iff.mpr ⟨_, _, h01, h12⟩
    exact Order.add_one_le_of_lt h1
  unfold ringKrullDim
  have hh' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ↑(Order.height (⟨maximalIdeal ↥N₀, (maximalIdeal.isMaximal ↥N₀).isPrime⟩ : PrimeSpectrum ↥N₀)) :=
    WithBot.coe_le_coe.mpr hh
  exact le_trans hh' (Order.height_le_krullDim _)

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

namespace NRU

theorem eq_or_eq_of_two_primes_of_crossing
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)
    (𝔭₁ 𝔭₂ : Ideal O) [𝔭₁.IsPrime] [𝔭₂.IsPrime] (h₁₂ : 𝔭₁ ≠ 𝔭₂)
    (ht₁ : t ∈ 𝔭₁) (ht₂ : t ∈ 𝔭₂) (h₁ : 𝔭₁ ≠ maximalIdeal O) (h₂ : 𝔭₂ ≠ maximalIdeal O)
    (𝔮 : Ideal O) [𝔮.IsPrime] (htq : t ∈ 𝔮) (hq : 𝔮 ≠ maximalIdeal O) :
    𝔮 = 𝔭₁ ∨ 𝔮 = 𝔭₂ := by
  classical
  by_cases hq₁ : 𝔮 = 𝔭₁
  · exact Or.inl hq₁
  right
  let SU : O → Prop := fun f =>
    ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)}
  let SV : O → Prop := fun f =>
    ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, V (π ^ w)}
  have key : ∀ (P P' : Ideal O) [P.IsPrime] [P'.IsPrime], P ≠ P' → t ∈ P → t ∈ P' →
      P ≠ maximalIdeal O → P' ≠ maximalIdeal O →
      ((∀ f, f ∈ P ↔ SU f) ∧ (∀ f, f ∈ P' ↔ SV f)) ∨ ((∀ f, f ∈ P ↔ SV f) ∧ (∀ f, f ∈ P' ↔ SU f)) :=
    fun P P' _ _ hne hP hP' hPm hP'm =>
      UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne π hπ w hw ι t ht P P' hne hP hP'
        hPm hP'm
  have ext_of : ∀ (P P' : Ideal O) (S : O → Prop), (∀ f, f ∈ P ↔ S f) → (∀ f, f ∈ P' ↔ S f) → P = P' :=
    fun P P' S h h' => Ideal.ext fun f => (h f).trans (h' f).symm
  rcases key 𝔭₁ 𝔭₂ h₁₂ ht₁ ht₂ h₁ h₂ with ⟨h1U, h2V⟩ | ⟨h1V, h2U⟩
  · rcases key 𝔮 𝔭₁ hq₁ htq ht₁ hq h₁ with ⟨hqU, -⟩ | ⟨hqV, -⟩
    · exact absurd (ext_of 𝔮 𝔭₁ SU hqU h1U) hq₁
    · exact ext_of 𝔮 𝔭₂ SV hqV h2V
  · rcases key 𝔮 𝔭₁ hq₁ htq ht₁ hq h₁ with ⟨hqU, -⟩ | ⟨hqV, -⟩
    · exact ext_of 𝔮 𝔭₂ SU hqU h2U
    · exact absurd (ext_of 𝔮 𝔭₁ SV hqV h1V) hq₁

theorem S1_core
    {F : Type} [Field F] (Lx : Subring F) [IsLocalRing ↥Lx]
    (Oi Oj : Subring F) [IsLocalRing ↥Oi] [IsLocalRing ↥Oj] (hLxi : Lx ≤ Oi) (hLxj : Lx ≤ Oj)
    (N₀ : Subring F) (hN₀L : N₀ ≤ Lx)
    (xN yN : F) (hxN : xN ∈ N₀) (hyN : yN ∈ N₀)
    (hx_nu : ¬ IsUnit (⟨xN, hLxi (hN₀L hxN)⟩ : ↥Oi)) (hx_u : IsUnit (⟨xN, hLxj (hN₀L hxN)⟩ : ↥Oj))
    (hy_nu : ¬ IsUnit (⟨yN, hLxj (hN₀L hyN)⟩ : ↥Oj)) (hy_u : IsUnit (⟨yN, hLxi (hN₀L hyN)⟩ : ↥Oi))
    (CA : Ideal ↥Lx → Prop)
    (hmax : ∀ Q : Ideal ↥Lx, Q.IsPrime → CA Q →
      (∀ (n : F) (hn : n ∈ N₀), ¬ IsUnit (⟨n, hn⟩ : ↥N₀) → (⟨n, hN₀L hn⟩ : ↥Lx) ∈ Q) → Q = maximalIdeal ↥Lx)
    (layers : ∀ S : Finset F, (∀ f ∈ S, f ∈ Lx) →
      ∃ (R : Subring F) (_ : IsNoetherianRing ↥R) (_ : IsLocalRing ↥R) (hNR : N₀ ≤ R) (hRL : R ≤ Lx)
        (t : F) (ht : t ∈ R)
        (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (maximalIdeal W) W) (π : W) (w : ℕ)
        (ι : AdicCompletion (maximalIdeal ↥R) ↥R ≃+* UVCrossingModel W (π ^ w)),
        (∀ f ∈ S, f ∈ R) ∧
        (∀ (n : F) (hn : n ∈ N₀), ¬ IsUnit (⟨n, hn⟩ : ↥N₀) → ¬ IsUnit (⟨n, hNR hn⟩ : ↥R)) ∧
        (∀ Q : Ideal ↥Lx, Q.IsPrime → CA Q → (⟨t, hRL ht⟩ : ↥Lx) ∈ Q) ∧
        ¬ IsUnit (⟨t, hLxi (hRL ht)⟩ : ↥Oi) ∧ ¬ IsUnit (⟨t, hLxj (hRL ht)⟩ : ↥Oj) ∧
        maximalIdeal W = Ideal.span {π} ∧ 1 ≤ w ∧
        ι (algebraMap ↥R (AdicCompletion (maximalIdeal ↥R) ↥R) ⟨t, ht⟩) = const (π ^ w) π) :
    ∀ Q : Ideal ↥Lx, Q.IsPrime → CA Q → Q ≠ maximalIdeal ↥Lx →
      Q = (maximalIdeal ↥Oi).comap (Subring.inclusion hLxi) ∨
      Q = (maximalIdeal ↥Oj).comap (Subring.inclusion hLxj) := by
  classical
  intro Q hQ hCA hQne
  haveI := hQ
  set Qi : Ideal ↥Lx := (maximalIdeal ↥Oi).comap (Subring.inclusion hLxi) with hQidef
  set Qj : Ideal ↥Lx := (maximalIdeal ↥Oj).comap (Subring.inclusion hLxj) with hQjdef
  have hmemQi : ∀ (f : F) (hf : f ∈ Lx), (⟨f, hf⟩ : ↥Lx) ∈ Qi ↔ ¬ IsUnit (⟨f, hLxi hf⟩ : ↥Oi) := by
    intro f hf; rw [hQidef, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]; rfl
  have hmemQj : ∀ (f : F) (hf : f ∈ Lx), (⟨f, hf⟩ : ↥Lx) ∈ Qj ↔ ¬ IsUnit (⟨f, hLxj hf⟩ : ↥Oj) := by
    intro f hf; rw [hQjdef, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]; rfl

  have step : ∀ S : Finset F, (∀ f ∈ S, f ∈ Lx) → ∃ (R : Subring F) (hRL : R ≤ Lx), (∀ f ∈ S, f ∈ R) ∧ xN ∈ R ∧
      ((∀ (f : F) (hf : f ∈ R), (⟨f, hRL hf⟩ : ↥Lx) ∈ Q ↔ (⟨f, hRL hf⟩ : ↥Lx) ∈ Qi) ∨
       (∀ (f : F) (hf : f ∈ R), (⟨f, hRL hf⟩ : ↥Lx) ∈ Q ↔ (⟨f, hRL hf⟩ : ↥Lx) ∈ Qj)) := by
    intro S hS
    obtain ⟨R, hRnoeth, hRloc, hNR, hRL, t, ht, W, _, _, _, _, π, w, ι, hSR, hlocN, htQ, hti, htj, hπ, hw, hιt⟩ :=
      layers S hS
    refine ⟨R, hRL, hSR, hNR hxN, ?_⟩

    let QR : Ideal ↥R := Q.comap (Subring.inclusion hRL)
    let P₁ : Ideal ↥R := (maximalIdeal ↥Oi).comap (Subring.inclusion (hRL.trans hLxi))
    let P₂ : Ideal ↥R := (maximalIdeal ↥Oj).comap (Subring.inclusion (hRL.trans hLxj))
    haveI : QR.IsPrime := Ideal.comap_isPrime _ _
    haveI : P₁.IsPrime := Ideal.comap_isPrime _ _
    haveI : P₂.IsPrime := Ideal.comap_isPrime _ _
    have hP₁ : ∀ (f : F) (hf : f ∈ R), (⟨f, hf⟩ : ↥R) ∈ P₁ ↔ ¬ IsUnit (⟨f, hLxi (hRL hf)⟩ : ↥Oi) := by
      intro f hf; rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]; rfl
    have hP₂ : ∀ (f : F) (hf : f ∈ R), (⟨f, hf⟩ : ↥R) ∈ P₂ ↔ ¬ IsUnit (⟨f, hLxj (hRL hf)⟩ : ↥Oj) := by
      intro f hf; rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]; rfl
    have hQR : ∀ (f : F) (hf : f ∈ R), (⟨f, hf⟩ : ↥R) ∈ QR ↔ (⟨f, hRL hf⟩ : ↥Lx) ∈ Q := by
      intro f hf; rw [Ideal.mem_comap]; rfl

    have hyN₀ : ¬ IsUnit (⟨yN, hyN⟩ : ↥N₀) := fun hu =>
      hy_nu (hu.map (Subring.inclusion (hN₀L.trans hLxj)))
    have hxN₀ : ¬ IsUnit (⟨xN, hxN⟩ : ↥N₀) := fun hu =>
      hx_nu (hu.map (Subring.inclusion (hN₀L.trans hLxi)))
    have hyR : (⟨yN, hNR hyN⟩ : ↥R) ∈ maximalIdeal ↥R :=
      (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hlocN yN hyN hyN₀))
    have hxR : (⟨xN, hNR hxN⟩ : ↥R) ∈ maximalIdeal ↥R :=
      (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hlocN xN hxN hxN₀))
    have h₁₂ : P₁ ≠ P₂ := by
      intro h
      have : (⟨xN, hNR hxN⟩ : ↥R) ∈ P₁ := (hP₁ xN _).2 hx_nu
      rw [h, hP₂] at this
      exact this hx_u
    have hP₁m : P₁ ≠ maximalIdeal ↥R := by
      intro h
      have : (⟨yN, hNR hyN⟩ : ↥R) ∈ P₁ := h ▸ hyR
      exact ((hP₁ yN _).1 this) hy_u
    have hP₂m : P₂ ≠ maximalIdeal ↥R := by
      intro h
      have : (⟨xN, hNR hxN⟩ : ↥R) ∈ P₂ := h ▸ hxR
      exact ((hP₂ xN _).1 this) hx_u
    have hQRm : QR ≠ maximalIdeal ↥R := by
      intro h
      apply hQne
      apply hmax Q hQ hCA
      intro n hn hnu
      have : (⟨n, hNR hn⟩ : ↥R) ∈ QR := by
        rw [h]; exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hlocN n hn hnu))
      exact (hQR n _).1 this
    have htQR : (⟨t, ht⟩ : ↥R) ∈ QR := (hQR t ht).2 (htQ Q hQ hCA)
    have ht₁ : (⟨t, ht⟩ : ↥R) ∈ P₁ := (hP₁ t ht).2 hti
    have ht₂ : (⟨t, ht⟩ : ↥R) ∈ P₂ := (hP₂ t ht).2 htj
    rcases eq_or_eq_of_two_primes_of_crossing π hπ w hw ι ⟨t, ht⟩ hιt P₁ P₂ h₁₂ ht₁ ht₂ hP₁m hP₂m QR htQR hQRm
      with h | h
    · left
      intro f hf
      rw [← hQR f hf, h, hP₁ f hf, hmemQi]
    · right
      intro f hf
      rw [← hQR f hf, h, hP₂ f hf, hmemQj]

  have hxi : (⟨xN, hN₀L hxN⟩ : ↥Lx) ∈ Qi := (hmemQi xN _).2 hx_nu
  have hxj : (⟨xN, hN₀L hxN⟩ : ↥Lx) ∉ Qj := fun h => ((hmemQj xN _).1 h) hx_u
  by_cases hxQ : (⟨xN, hN₀L hxN⟩ : ↥Lx) ∈ Q
  · left
    ext f
    obtain ⟨R, hRL, hSR, hxR, hR⟩ := step {(f : F), xN} (by
      intro g hg
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact f.2
      · rw [Finset.mem_singleton.1 hg]; exact hN₀L hxN)
    have hfR : (f : F) ∈ R := hSR _ (Finset.mem_insert_self _ _)
    rcases hR with h | h
    · exact h (f : F) hfR
    · exact absurd ((h xN hxR).1 hxQ) hxj
  · right
    ext f
    obtain ⟨R, hRL, hSR, hxR, hR⟩ := step {(f : F), xN} (by
      intro g hg
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact f.2
      · rw [Finset.mem_singleton.1 hg]; exact hN₀L hxN)
    have hfR : (f : F) ∈ R := hSR _ (Finset.mem_insert_self _ _)
    rcases hR with h | h
    · exact absurd ((h xN hxR).2 hxi) hxQ
    · exact h (f : F) hfR

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

namespace NRU

theorem S1_assembly
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (ηi ηj : X)
    (hηi : toBase.base ηi = closedPoint ↥A) (hηj : toBase.base ηj = closedPoint ↥A)
    (N₀ : Subring F) [IsLocalRing ↥N₀]
    (hNi : N₀ ≤ SemistableModel.localRing X φ ηi) (hNj : N₀ ≤ SemistableModel.localRing X φ ηj)
    (xN yN : F) (hxN : xN ∈ N₀) (hyN : yN ∈ N₀)
    (hx_nu : ¬ ∃ g ∈ SemistableModel.localRing X φ ηi, xN * g = 1)
    (hx_u : ∃ g ∈ SemistableModel.localRing X φ ηj, xN * g = 1)
    (hy_nu : ¬ ∃ g ∈ SemistableModel.localRing X φ ηj, yN * g = 1)
    (hy_u : ∃ g ∈ SemistableModel.localRing X φ ηi, yN * g = 1)
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (𝔭 : Ideal ↥T) [h𝔭p : 𝔭.IsPrime]
    (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))

    (S6i : ∀ t : ↥T, t ∉ 𝔭 → ∃ g ∈ SemistableModel.localRing X φ ηi, (t : F) * g = 1)
    (S6j : ∀ t : ↥T, t ∉ 𝔭 → ∃ g ∈ SemistableModel.localRing X φ ηj, (t : F) * g = 1)

    (layers : ∀ (S : Finset F), (∀ f ∈ S, f ∈ (LocalSubring.ofPrime T 𝔭).toSubring) →
      ∃ (R : Subring F) (_ : IsNoetherianRing ↥R) (_ : IsLocalRing ↥R) (hNR : N₀ ≤ R) (hRL : R ≤ (LocalSubring.ofPrime T 𝔭).toSubring)
        (c : ↥A) (hc : algebraMap L F (c : L) ∈ R)
        (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W)
        (π : W) (w : ℕ) (ι : AdicCompletion (maximalIdeal ↥R) ↥R ≃+* UVCrossingModel W (π ^ w)),
        (∀ f ∈ S, f ∈ R) ∧
        (∀ f : ↥N₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion hNR f)) ∧
        c ∈ maximalIdeal ↥A ∧ Irreducible π ∧ 1 ≤ w ∧
        ι (algebraMap ↥R _ ⟨algebraMap L F (c : L), hc⟩) = const (π ^ w) π ∧
        IsIntegrallyClosed ↥R ∧
        (∀ (Q : Ideal ↥R) [Q.IsPrime], (⟨algebraMap L F (c : L), hc⟩ : ↥R) ∈ Q → Q ≠ maximalIdeal ↥R →
          IsDiscreteValuationRing (Localization.AtPrime Q))) :
    ∀ 𝔮 : Ideal ↥T, 𝔮.IsPrime →
      (∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ T), a ∈ maximalIdeal ↥A →
        (⟨algebraMap L F (a : L), h⟩ : ↥T) ∈ 𝔮) →
      𝔮 ≤ 𝔭 → 𝔮 ≠ 𝔭 →
      (∀ t : ↥T, t ∈ 𝔮 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ ηi, (t : F) * g = 1) ∨
      (∀ t : ↥T, t ∈ 𝔮 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ ηj, (t : F) * g = 1) := by
  classical
  intro 𝔮 h𝔮 h𝔮A h𝔮𝔭 h𝔮ne
  haveI := h𝔮

  have hTLx : T ≤ (LocalSubring.ofPrime T 𝔭).toSubring := fun f hf => LocalSubring.le_ofPrime T 𝔭 hf
  have hAT : ∀ a : ↥A, algebraMap L F (a : L) ∈ T := fun a =>
    hT ▸ Subring.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)
  have hN₀T : N₀ ≤ T := fun f hf => hT ▸ Subring.subset_closure (Set.mem_union_left _ hf)
  have hTi : T ≤ SemistableModel.localRing X φ ηi := NRU.closure_le_localRing A X toBase φ hφ N₀ T hT ηi hNi
  have hTj : T ≤ SemistableModel.localRing X φ ηj := NRU.closure_le_localRing A X toBase φ hφ N₀ T hT ηj hNj

  haveI hlocX : ∀ z : X, IsLocalRing ↥(SemistableModel.localRing X φ z) := fun z =>
    IsLocalRing.of_surjective' (NRU345.locEquiv φ z).toRingHom (NRU345.locEquiv φ z).surjective
  have hunit : ∀ (η : X) (f : F) (hf : f ∈ SemistableModel.localRing X φ η),
      IsUnit (⟨f, hf⟩ : ↥(SemistableModel.localRing X φ η)) ↔ ∃ g ∈ SemistableModel.localRing X φ η, f * g = 1 := by
    intro η f hf
    constructor
    · intro hu
      exact ⟨_, (hu.unit⁻¹ : (↥(SemistableModel.localRing X φ η))ˣ).1.2, congrArg Subtype.val hu.mul_val_inv⟩
    · rintro ⟨g, hg, hfg⟩
      exact IsUnit.of_mul_eq_one (b := ⟨g, hg⟩) (Subtype.ext hfg)

  have hLx_le : ∀ (η : X), T ≤ SemistableModel.localRing X φ η →
      (∀ t : ↥T, t ∉ 𝔭 → ∃ g ∈ SemistableModel.localRing X φ η, (t : F) * g = 1) →
      (LocalSubring.ofPrime T 𝔭).toSubring ≤ SemistableModel.localRing X φ η := by
    intro η hTη S6 f hf
    obtain ⟨b, c, hc, hfc⟩ := (NRU.mem_ofPrime_iff T 𝔭 f).1 hf
    obtain ⟨g, hg, hcg⟩ := S6 c hc
    have : f = (b : F) * g := by
      calc f = f * ((c : F) * g) := by rw [hcg, mul_one]
        _ = (f * (c : F)) * g := by ring
        _ = (b : F) * g := by rw [hfc]
    rw [this]
    exact mul_mem (hTη b.2) hg
  have hLxi : (LocalSubring.ofPrime T 𝔭).toSubring ≤ SemistableModel.localRing X φ ηi := hLx_le ηi hTi S6i
  have hLxj : (LocalSubring.ofPrime T 𝔭).toSubring ≤ SemistableModel.localRing X φ ηj := hLx_le ηj hTj S6j

  haveI : IsLocalization.AtPrime ↥(LocalSubring.ofPrime T 𝔭).toSubring 𝔭 := inferInstance
  have hdisj : Disjoint (𝔭.primeCompl : Set ↥T) (𝔮 : Set ↥T) := by
    rw [Set.disjoint_left]
    intro t ht htq
    exact ht (h𝔮𝔭 htq)
  let Q : Ideal ↥(LocalSubring.ofPrime T 𝔭).toSubring := 𝔮.map (algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring)
  haveI hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl _ 𝔮 h𝔮 hdisj
  have hQcomap : Q.comap (algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring) = 𝔮 :=
    IsLocalization.comap_map_of_isPrime_disjoint 𝔭.primeCompl _ h𝔮 hdisj
  have hmemQT : ∀ t : ↥T, (⟨(t : F), hTLx t.2⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∈ Q ↔ t ∈ 𝔮 := by
    intro t
    rw [← hQcomap, Ideal.mem_comap]
    rfl

  let CA : Ideal ↥(LocalSubring.ofPrime T 𝔭).toSubring → Prop := fun Q' =>
    ∀ a : ↥A, a ∈ maximalIdeal ↥A → (⟨algebraMap L F (a : L), hTLx (hAT a)⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∈ Q'
  have hCAQ : CA Q := fun a ha => (hmemQT ⟨_, hAT a⟩).2 (h𝔮A a (hAT a) ha)
  have hQne : Q ≠ maximalIdeal ↥(LocalSubring.ofPrime T 𝔭).toSubring := by
    intro h
    apply h𝔮ne
    refine le_antisymm h𝔮𝔭 fun t ht => ?_
    rw [← hmemQT, h]
    exact (NRU.mem_maximalIdeal_ofPrime_iff T 𝔭 t).2 ht
  have hmax : ∀ Q' : Ideal ↥(LocalSubring.ofPrime T 𝔭).toSubring, Q'.IsPrime → CA Q' →
      (∀ (n : F) (hn : n ∈ N₀), ¬ IsUnit (⟨n, hn⟩ : ↥N₀) → (⟨n, hTLx (hN₀T hn)⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∈ Q') →
      Q' = maximalIdeal ↥(LocalSubring.ofPrime T 𝔭).toSubring := by
    intro Q' hQ' hCA' hN'
    haveI := hQ'
    refine le_antisymm (IsLocalRing.le_maximalIdeal hQ'.ne_top) ?_

    have h𝔭Q' : Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
        {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}) ≤
        Q'.comap (algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring) := by
      refine Ideal.span_le.2 ?_
      rintro t (⟨f, hf, htf⟩ | ⟨a, ha, hta⟩)
      · rw [SetLike.mem_coe, Ideal.mem_comap]
        have : algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring t = ⟨(f : F), hTLx (hN₀T f.2)⟩ := Subtype.ext htf
        rw [this]
        exact hN' f f.2 (by simpa using hf)
      · rw [SetLike.mem_coe, Ideal.mem_comap]
        have : algebraMap ↥T ↥(LocalSubring.ofPrime T 𝔭).toSubring t = ⟨algebraMap L F (a : L), hTLx (hAT a)⟩ := Subtype.ext hta
        rw [this]
        exact hCA' a ha
    intro f hf
    obtain ⟨b, c, hc, hfc⟩ := (NRU.mem_ofPrime_iff T 𝔭 (f : F)).1 f.2
    have hb : b ∈ 𝔭 := (NRU.not_isUnit_ofPrime_iff T 𝔭 (f : F) b c hc hfc f.2).1
      (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hf))
    have hbQ' : (⟨(b : F), hTLx b.2⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∈ Q' := by
      have := h𝔭Q' (h𝔭 ▸ hb : b ∈ Ideal.span _); rw [Ideal.mem_comap] at this; exact this

    have hcu : IsUnit (⟨(c : F), hTLx c.2⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) := by
      have := (NRU.mem_maximalIdeal_ofPrime_iff T 𝔭 c).not.2 hc
      rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at this
    have : f = ⟨(b : F), hTLx b.2⟩ * ((hcu.unit⁻¹ : (↥(LocalSubring.ofPrime T 𝔭).toSubring)ˣ) : ↥(LocalSubring.ofPrime T 𝔭).toSubring) := by
      have h1 : f * ⟨(c : F), hTLx c.2⟩ = ⟨(b : F), hTLx b.2⟩ := Subtype.ext hfc
      rw [← h1, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Q'.mul_mem_right _ hbQ'
  have hx_nu' : ¬ IsUnit (⟨xN, hLxi (hTLx (hN₀T hxN))⟩ : ↥(SemistableModel.localRing X φ ηi)) :=
    fun h => hx_nu ((hunit ηi xN _).1 h)
  have hx_u' : IsUnit (⟨xN, hLxj (hTLx (hN₀T hxN))⟩ : ↥(SemistableModel.localRing X φ ηj)) :=
    (hunit ηj xN _).2 hx_u
  have hy_nu' : ¬ IsUnit (⟨yN, hLxj (hTLx (hN₀T hyN))⟩ : ↥(SemistableModel.localRing X φ ηj)) :=
    fun h => hy_nu ((hunit ηj yN _).1 h)
  have hy_u' : IsUnit (⟨yN, hLxi (hTLx (hN₀T hyN))⟩ : ↥(SemistableModel.localRing X φ ηi)) :=
    (hunit ηi yN _).2 hy_u
  have layers' : ∀ S : Finset F, (∀ f ∈ S, f ∈ (LocalSubring.ofPrime T 𝔭).toSubring) →
      ∃ (R : Subring F) (_ : IsNoetherianRing ↥R) (_ : IsLocalRing ↥R) (hNR : N₀ ≤ R) (hRL : R ≤ (LocalSubring.ofPrime T 𝔭).toSubring)
        (t : F) (ht : t ∈ R)
        (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (maximalIdeal W) W) (π : W) (w : ℕ)
        (ι : AdicCompletion (maximalIdeal ↥R) ↥R ≃+* UVCrossingModel W (π ^ w)),
        (∀ f ∈ S, f ∈ R) ∧
        (∀ (n : F) (hn : n ∈ N₀), ¬ IsUnit (⟨n, hn⟩ : ↥N₀) → ¬ IsUnit (⟨n, hNR hn⟩ : ↥R)) ∧
        (∀ Q' : Ideal ↥(LocalSubring.ofPrime T 𝔭).toSubring, Q'.IsPrime → CA Q' → (⟨t, hRL ht⟩ : ↥(LocalSubring.ofPrime T 𝔭).toSubring) ∈ Q') ∧
        ¬ IsUnit (⟨t, hLxi (hRL ht)⟩ : ↥(SemistableModel.localRing X φ ηi)) ∧
        ¬ IsUnit (⟨t, hLxj (hRL ht)⟩ : ↥(SemistableModel.localRing X φ ηj)) ∧
        maximalIdeal W = Ideal.span {π} ∧ 1 ≤ w ∧
        ι (algebraMap ↥R (AdicCompletion (maximalIdeal ↥R) ↥R) ⟨t, ht⟩) = const (π ^ w) π := by
    intro S hS
    obtain ⟨R, hRn, hRl, hNR, hRL, c, hc, W, iW1, iW2, iW3, iW4, π, w, ι, hSR, hloc, hc𝔪, hπirr, hw, hιc, -, -⟩ :=
      layers S hS
    letI := iW1; letI := iW2; letI := iW3; letI := iW4
    refine ⟨R, hRn, hRl, hNR, hRL, algebraMap L F (c : L), hc, W, iW1, iW2, iW3, iW4, π, w, ι, hSR,
      fun n hn hnu => hloc ⟨n, hn⟩ hnu, fun Q' _ hCA' => hCA' c hc𝔪, ?_, ?_, ?_, hw, hιc⟩
    · exact not_isUnit_const_of_mem_maximalIdeal A X toBase φ hφ ηi hηi c hc𝔪 _
    · exact not_isUnit_const_of_mem_maximalIdeal A X toBase φ hφ ηj hηj c hc𝔪 _
    · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr

  have core := NRU.S1_core (LocalSubring.ofPrime T 𝔭).toSubring (SemistableModel.localRing X φ ηi) (SemistableModel.localRing X φ ηj)
    hLxi hLxj N₀ (fun f hf => hTLx (hN₀T hf)) xN yN hxN hyN hx_nu' hx_u' hy_nu' hy_u' CA hmax layers' Q hQp hCAQ hQne

  rcases core with h | h
  · left
    intro t
    rw [← hmemQT, h, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (⟨(t : F), hTi t.2⟩ : ↥(SemistableModel.localRing X φ ηi)) ↔ _
    rw [hunit]
  · right
    intro t
    rw [← hmemQT, h, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (⟨(t : F), hTj t.2⟩ : ↥(SemistableModel.localRing X φ ηj)) ↔ _
    rw [hunit]

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

namespace NRU

theorem S6 {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (hval : ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      ∃ V : ValuationSubring F, V.toSubring = SemistableModel.localRing X φ η)
    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)
    (N₀ : Subring F) [IsLocalRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (𝔭 : Ideal ↥T)
    (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))
    (hϖ'0 : ϖ' ≠ 0)
    (η : X) (hη : toBase.base η = closedPoint ↥A) (hη' : ∃ y : X, η ⤳ y ∧ y ≠ η)
    (hTη : T ≤ SemistableModel.localRing X φ η) (t : ↥T) (ht : t ∉ 𝔭) :
    ∃ g ∈ SemistableModel.localRing X φ η, (t : F) * g = 1 := by
  classical
  have hunitS : ∀ (S : Subring F) (f : F) (hf : f ∈ S), IsUnit (⟨f, hf⟩ : ↥S) ↔ ∃ g ∈ S, f * g = 1 := by
    intro S f hf
    constructor
    · intro hu
      obtain ⟨u, hu⟩ := hu
      refine ⟨((u⁻¹ : (↥S)ˣ) : ↥S), ((u⁻¹ : (↥S)ˣ) : ↥S).2, ?_⟩
      have := congrArg (fun z : ↥S => (z : F)) u.mul_inv
      simpa [hu] using this
    · rintro ⟨g, hg, hfg⟩
      exact isUnit_iff_exists_inv.mpr ⟨⟨g, hg⟩, Subtype.ext (by simpa using hfg)⟩
  obtain ⟨V, hV⟩ := hval η hη hη'
  have hmemV : ∀ f : F, f ∈ V ↔ f ∈ SemistableModel.localRing X φ η := fun f => by rw [← hV]; rfl
  by_contra hno
  let incl : ↥T →+* ↥V :=
    { toFun := fun s => ⟨(s : F), (hmemV _).mpr (hTη s.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let 𝔮 : Ideal ↥T := (maximalIdeal ↥V).comap incl
  haveI : 𝔮.IsPrime := Ideal.comap_isPrime incl _
  have hVunit : ∀ (f : F) (hf : f ∈ V), IsUnit (⟨f, hf⟩ : ↥V) ↔ ∃ g ∈ SemistableModel.localRing X φ η, f * g = 1 := by
    intro f hf
    have h1 : IsUnit (⟨f, hf⟩ : ↥V.toSubring) ↔ ∃ g ∈ V.toSubring, f * g = 1 := hunitS V.toSubring f hf
    exact h1.trans ⟨fun ⟨g, hg, e⟩ => ⟨g, (hmemV g).mp hg, e⟩, fun ⟨g, hg, e⟩ => ⟨g, (hmemV g).mpr hg, e⟩⟩
  have h𝔮A : ∀ a : ↥A, a ∈ maximalIdeal ↥A →
      (⟨algebraMap L F (a : L), NRU.algebraMap_mem_T A N₀ T hT a⟩ : ↥T) ∈ 𝔮 := by
    intro a ha
    show incl _ ∈ maximalIdeal ↥V
    rw [mem_maximalIdeal, mem_nonunits_iff, hVunit]
    have hmem : algebraMap L F (a : L) ∈ SemistableModel.localRing X φ η := hTη (NRU.algebraMap_mem_T A N₀ T hT a)
    show ¬ ∃ g ∈ SemistableModel.localRing X φ η, algebraMap L F (a : L) * g = 1
    rw [← hunitS _ _ hmem]
    exact NRU.not_isUnit_const_of_mem_maximalIdeal A X toBase φ hφ η hη a ha hmem
  have ht𝔮 : t ∈ 𝔮 := by
    show incl t ∈ maximalIdeal ↥V
    rw [mem_maximalIdeal, mem_nonunits_iff, hVunit]
    exact hno
  exact ht (NRU.le_p_of_isPrime A C' hC'A ϖ' hϖ' N₀ hC'N₀ hconst hlin T hT 𝔭 h𝔭 halg hϖ'0 𝔮 h𝔮A ht𝔮)

end NRU
p2m_reactivate "P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU345 P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.NRU"

theorem solution

    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (ηi ηj x : X) (hij : ηi ≠ ηj) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (hxns : x ∉ toBase.smoothLocus) (hi : ηi ⤳ x) (hj : ηj ⤳ x)
    (hηi : toBase.base ηi = closedPoint ↥A) (hηj : toBase.base ηj = closedPoint ↥A)
    (hηi' : ∃ y : X, ηi ⤳ y ∧ y ≠ ηi) (hηj' : ∃ y : X, ηj ⤳ y ∧ y ≠ ηj)
    (honly : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = ηi ∨ η = ηj)

    (hval : ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      ∃ V : ValuationSubring F, V.toSubring = SemistableModel.localRing X φ η)

    (huniq : ∀ x' : X, toBase.base x' = closedPoint ↥A → (∀ y : X, x' ⤳ y → y = x') → ηi ⤳ x' → ηj ⤳ x' → x' = x)

    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)
    (N₀ : Subring F) [IsLocalRing ↥N₀] [IsNoetherianRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (hNi : N₀ ≤ SemistableModel.localRing X φ ηi) (hNj : N₀ ≤ SemistableModel.localRing X φ ηj)

    (xN yN uN : F) (hxN : xN ∈ N₀) (hyN : yN ∈ N₀) (huN : ∃ hu : uN ∈ N₀, IsUnit (⟨uN, hu⟩ : ↥N₀))
    (ϖ₀ : L) (hϖ₀C : ϖ₀ ∈ C') (hϖ₀ : ϖ₀ ≠ 0) (E₀ : ℕ)
    (hxy : xN * yN = algebraMap L F ϖ₀ ^ E₀ * uN)
    (hmod : ∃ h : ϖ₀ ^ E₀ ∈ A, (⟨ϖ₀ ^ E₀, h⟩ : ↥A) ∈ maximalIdeal ↥A)
    (hx_nu : ¬ ∃ g ∈ SemistableModel.localRing X φ ηi, xN * g = 1)
    (hx_u : ∃ g ∈ SemistableModel.localRing X φ ηj, xN * g = 1)
    (hy_nu : ¬ ∃ g ∈ SemistableModel.localRing X φ ηj, yN * g = 1)
    (hy_u : ∃ g ∈ SemistableModel.localRing X φ ηi, yN * g = 1)

    (Wc : Type) [CommRing Wc] [IsDomain Wc] [IsDiscreteValuationRing Wc] [IsAdicComplete (maximalIdeal Wc) Wc]
    (πW : Wc) (hirr : Irreducible πW) (E : ℕ) (hE : 1 ≤ E)
    (σ : Wc →+* AdicCompletion (maximalIdeal ↥N₀) ↥N₀)
    (ιc : AdicCompletion (maximalIdeal ↥N₀) ↥N₀ ≃+* UVCrossingModel Wc (πW ^ E))
    (hσπ : ∀ h : algebraMap L F ((ϖ' : ↥C') : L) ∈ N₀,
      σ πW = algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀) ⟨_, h⟩)
    (hισ : ∀ o : Wc, ιc (σ o) = const (πW ^ E) o)
    (hσC : ∀ (c : ↥C') (h : algebraMap L F (c : L) ∈ N₀),
      ∃ o : Wc, σ o = algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀) ⟨_, h⟩)

    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (hfrac : ∀ f : F, ∃ b c : ↥T, (c : F) ≠ 0 ∧ f * (c : F) = (b : F))
    (𝔭 : Ideal ↥T)
    (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))

    (Bx : Subring F) (hBxN₀ : ∀ f : F, f ∈ Bx → f ∈ N₀)
    (hxB : xN ∈ Bx) (hyB : yN ∈ Bx) (huB : uN ∈ Bx)
    (hN₀Bx : ∀ f : F, f ∈ N₀ ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ N₀, IsUnit (⟨h, hh⟩ : ↥N₀)) ∧ f * h = g)
    (hBxfg : ∃ T : Finset F, Bx = Subring.closure
      ({f : F | ∃ c : L, c ∈ C' ∧ f = algebraMap L F c} ∪ (↑T : Set F)))

    (hcent : ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      Bx ≤ SemistableModel.localRing X φ η →
        ∃ f ∈ Bx, (∀ hf : f ∈ N₀, ¬ IsUnit (⟨f, hf⟩ : ↥N₀)) ∧ ∃ g ∈ SemistableModel.localRing X φ η, f * g = 1)
    :
    ∀ 𝔮 : Ideal ↥T, 𝔮.IsPrime →
      (∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ T), a ∈ maximalIdeal ↥A →
        (⟨algebraMap L F (a : L), h⟩ : ↥T) ∈ 𝔮) →
      𝔮 ≤ 𝔭 → 𝔮 ≠ 𝔭 →
      (∀ t : ↥T, t ∈ 𝔮 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ ηi, (t : F) * g = 1) ∨
      (∀ t : ↥T, t ∈ 𝔮 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ ηj, (t : F) * g = 1) := by
  classical
  have hϖ'irr : Irreducible ϖ' := NRU.irreducible_of_residue_iff_of_pow_mem A C' hC'A ϖ' hϖ' ϖ₀ hϖ₀C hϖ₀ E₀ hmod
  have hϖ'0 : ϖ' ≠ 0 := hϖ'irr.ne_zero
  haveI h𝔭max : 𝔭.IsMaximal := NRU.isMaximal_p A C' hC'A ϖ' hϖ' N₀ hC'N₀ hconst hlin T hT 𝔭 h𝔭 hϖ'0
  haveI h𝔭p : 𝔭.IsPrime := h𝔭max.isPrime
  haveI hlocX : ∀ z : X, IsLocalRing ↥(SemistableModel.localRing X φ z) := fun z =>
    IsLocalRing.of_surjective' (NRU345.locEquiv φ z).toRingHom (NRU345.locEquiv φ z).surjective
  have hdim : 2 ≤ ringKrullDim ↥N₀ :=
    NRU.two_le_ringKrullDim_of_branches N₀ (SemistableModel.localRing X φ ηi) (SemistableModel.localRing X φ ηj)
      hNi hNj xN yN hxN hyN hx_nu hx_u hy_nu hy_u
  have hTi : T ≤ SemistableModel.localRing X φ ηi := NRU.closure_le_localRing A X toBase φ hφ N₀ T hT ηi hNi
  have hTj : T ≤ SemistableModel.localRing X φ ηj := NRU.closure_le_localRing A X toBase φ hφ N₀ T hT ηj hNj
  have S6i : ∀ t : ↥T, t ∉ 𝔭 → ∃ g ∈ SemistableModel.localRing X φ ηi, (t : F) * g = 1 := fun t ht =>
    NRU.S6 A X toBase φ hφ hval C' hC'A ϖ' hϖ' halg N₀ hC'N₀ hconst hlin T hT 𝔭 h𝔭 hϖ'0 ηi hηi hηi' hTi t ht
  have S6j : ∀ t : ↥T, t ∉ 𝔭 → ∃ g ∈ SemistableModel.localRing X φ ηj, (t : F) * g = 1 := fun t ht =>
    NRU.S6 A X toBase φ hφ hval C' hC'A ϖ' hϖ' halg N₀ hC'N₀ hconst hlin T hT 𝔭 h𝔭 hϖ'0 ηj hηj hηj' hTj t ht
  have layers := fun (S : Finset F) (hS : ∀ f ∈ S, f ∈ (LocalSubring.ofPrime T 𝔭).toSubring) =>
    NRU.Layers.exists_layer A C' hC'A ϖ' hϖ' hϖ'irr halg N₀ hC'N₀ hconst hlin hdim Wc πW hirr E hE σ ιc hσπ hισ hσC
      T hT hfrac 𝔭 h𝔭 (LocalSubring.ofPrime T 𝔭).toSubring (NRU.mem_ofPrime_iff T 𝔭) S hS
  exact NRU.S1_assembly A X toBase φ hφ ηi ηj hηi hηj N₀ hNi hNj xN yN hxN hyN hx_nu hx_u hy_nu hy_u T hT 𝔭 h𝔭
    S6i S6j layers

#print axioms solution

end S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart
end P2MW
export P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart (solution)
