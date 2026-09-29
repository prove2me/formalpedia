-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c59bb740-cbd7-5d04-855f-6a174bc9dd38

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.IdealSheafData.ideal_mul Scheme.IdealSheafData.support_comap Scheme.Hom Scheme.Hom.germ_stalkMap_apply IsFinite Scheme.Hom.support_ker Spec IsIntegral Scheme.IdealSheafData.range_subschemeι StructureSheaf.stalkIso Scheme IsClosedImmersion Scheme.mem_zeroLocus_iff Scheme.Hom.ker_apply Scheme.IdealSheafData.map_ideal_basicOpen Scheme.Hom.app_eq_appLE Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.IdealSheafData.ker_subschemeι_app Scheme.IdealSheafData Scheme.IdealSheafData.ideal_comap_of_le Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal"
namespace S1Y
p2m_open "AlgebraicGeometry"

theorem mem_support_of_map_germ_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) {x : X} (V : X.affineOpens)
    (hxV : x ∈ (V : X.Opens))
    (h : Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) ≠ ⊤) : x ∈ I.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hxV, Scheme.mem_zeroLocus_iff]
  intro f hf hxf
  exact h (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf) ((X.mem_basicOpen f x hxV).mp hxf))

theorem not_mem_support_of_map_germ_eq_top {X : Scheme.{u}} (I : X.IdealSheafData) {x : X} (V : X.affineOpens)
    (hxV : x ∈ (V : X.Opens))
    (h : Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) = ⊤) : x ∉ I.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hxV, Scheme.mem_zeroLocus_iff]
  intro hall

  have hle : Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hall f hf ((X.mem_basicOpen f x hxV).mpr hu)
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))

theorem map_mem_nonZeroDivisors_basicOpen {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    {g : Γ(X, U)} (hg : g ∈ nonZeroDivisors Γ(X, U)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f) := by
  letI := U.2.isLocalization_basicOpen f
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers f) (S := Γ(X, X.basicOpen f)) hg

theorem isInvertible_comap_subschemeι_of_isIntegral {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) [IsIntegral J.subscheme] {η : Y} (hηJ : η ∈ J.support) (hηI : η ∉ I.support) :
    (I.comap J.subschemeι).IsInvertible := by
  intro w₀
  set y : Y := J.subschemeι w₀ with hydef
  obtain ⟨U, f, hyf, g, hg, hIg⟩ := hI y
  let D : Y.affineOpens := Y.affineBasicOpen f
  have hyD : y ∈ (D : Y.Opens) := hyf
  let E : (J.subscheme).affineOpens := ⟨J.subschemeι ⁻¹ᵁ (D : Y.Opens), D.2.preimage J.subschemeι⟩
  have hwE : w₀ ∈ (E : (J.subscheme).Opens) := hyD
  let gW : Γ(J.subscheme, E) := (J.subschemeι.appLE (D : Y.Opens) (E : (J.subscheme).Opens) le_rfl).hom g
  have hKE : (I.comap J.subschemeι).ideal E = Ideal.span {gW} := by
    rw [Scheme.IdealSheafData.ideal_comap_of_le I J.subschemeι D E le_rfl, hIg, Ideal.map_span,
      Set.image_singleton]

  haveI : Nonempty (E : (J.subscheme).Opens) := ⟨⟨w₀, hwE⟩⟩
  have hgW0 : gW ≠ 0 := by
    intro h0

    have happ : J.subschemeι.appLE (D : Y.Opens) (E : (J.subscheme).Opens) le_rfl = J.subschemeι.app (D : Y.Opens) :=
      (Scheme.Hom.app_eq_appLE _).symm
    have hgJ : g ∈ J.ideal D := by
      rw [← Scheme.IdealSheafData.ker_subschemeι_app J D, RingHom.mem_ker, ← happ]
      exact h0
    have hIJ : I.ideal D ≤ J.ideal D := by
      rw [hIg, Ideal.span_singleton_le_iff_mem]
      exact hgJ

    have hsub : ∀ z : Y, z ∈ (D : Y.Opens) → z ∈ J.support → z ∈ I.support := by
      intro z hzD hzJ
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := D) hzD] at hzJ ⊢
      exact Y.zeroLocus_mono hIJ hzJ

    have hirr : IsPreirreducible ((J.support : Set Y)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.image _
        J.subschemeι.base.hom.continuous.continuousOn
    have hyJ : y ∈ (J.support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w₀, rfl⟩
    obtain ⟨z, hzJ, hzD, hzI⟩ := hirr (D : Y.Opens) ((I.support : Set Y)ᶜ) (D : Y.Opens).isOpen
      I.support.isClosed.isOpen_compl ⟨y, hyJ, hyD⟩ ⟨η, hηJ, hηI⟩
    exact hzI (hsub z hzD hzJ)
  have hgW : gW ∈ nonZeroDivisors Γ(J.subscheme, E) := mem_nonZeroDivisors_of_ne_zero hgW0
  refine ⟨E, 1, ?_, ((J.subscheme).presheaf.map (homOfLE ((J.subscheme).basicOpen_le (1 : Γ(J.subscheme, E)))).op).hom gW,
    map_mem_nonZeroDivisors_basicOpen E 1 hgW, ?_⟩
  · rw [(J.subscheme).basicOpen_of_isUnit isUnit_one]; exact hwE
  · rw [← (I.comap J.subschemeι).map_ideal_basicOpen E 1, hKE, Ideal.map_span, Set.image_singleton]
    rfl

theorem map_maximalIdeal_of_surjective {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) :
    Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B := by
  refine le_antisymm ?_ ?_
  · exact ((IsLocalRing.local_hom_TFAE φ).out 0 2).mp ‹IsLocalHom φ›
  · intro b hb
    obtain ⟨a, rfl⟩ := hφ b
    refine Ideal.mem_map_of_mem _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    exact fun ha => hb (ha.map φ)

theorem map_germ_comap_eq_maximalIdeal {X : Scheme.{u}} (I J : X.IdealSheafData) (z : J.subscheme)
    (U : X.affineOpens) (hU : J.subschemeι z ∈ (U : X.Opens))
    (h : Ideal.map (X.presheaf.germ (U : X.Opens) (J.subschemeι z) hU).hom (I.ideal U ⊔ J.ideal U) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (J.subschemeι z))) :
    Ideal.map ((J.subscheme).presheaf.germ (J.subschemeι ⁻¹ᵁ (U : X.Opens)) z hU).hom
        ((I.comap J.subschemeι).ideal ⟨J.subschemeι ⁻¹ᵁ (U : X.Opens), U.2.preimage J.subschemeι⟩) =
      IsLocalRing.maximalIdeal ((J.subscheme).presheaf.stalk z) := by
  set E : (J.subscheme).affineOpens := ⟨J.subschemeι ⁻¹ᵁ (U : X.Opens), U.2.preimage J.subschemeι⟩ with hEdef

  have hsurj : Function.Surjective (J.subschemeι.stalkMap z).hom := J.subschemeι.stalkMap_surjective z
  rw [← map_maximalIdeal_of_surjective (J.subschemeι.stalkMap z).hom hsurj, ← h, Ideal.map_map, Ideal.map_sup]

  have hcomp : (J.subschemeι.stalkMap z).hom.comp (X.presheaf.germ (U : X.Opens) (J.subschemeι z) hU).hom =
      ((J.subscheme).presheaf.germ (J.subschemeι ⁻¹ᵁ (U : X.Opens)) z hU).hom.comp
        (J.subschemeι.app (U : X.Opens)).hom := by
    ext a
    exact Scheme.Hom.germ_stalkMap_apply J.subschemeι (U : X.Opens) z hU a
  rw [hcomp, ← Ideal.map_map, ← Ideal.map_map, Scheme.IdealSheafData.ideal_comap_of_le I J.subschemeι U E le_rfl,
    ← Scheme.Hom.app_eq_appLE]

  have hJ : Ideal.map (J.subschemeι.app (U : X.Opens)).hom (J.ideal U) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot, ← RingHom.mem_ker, Scheme.IdealSheafData.ker_subschemeι_app]
    exact ha
  rw [hJ, Ideal.map_bot, sup_bot_eq]

theorem mem_support_comap_iff {X : Scheme.{u}} (I J : X.IdealSheafData) (z : J.subscheme) :
    z ∈ (I.comap J.subschemeι).support ↔ J.subschemeι z ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

theorem support_ker_eq_range {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    ((f.ker).support : Set Y) = Set.range f.base := by
  rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]

theorem isUnit_natCast_stalk_of_not_mem {O : Type u} [CommRing O] (t : PrimeSpectrum O) {p : ℕ}
    (hp : ((p : ℕ) : O) ∉ t.asIdeal) : IsUnit ((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk t) := by
  let e := (StructureSheaf.stalkIso O t).toRingEquiv
  have h1 : IsUnit ((p : ℕ) : Localization.AtPrime t.asIdeal) := by
    rw [← map_natCast (algebraMap O (Localization.AtPrime t.asIdeal)) p]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime t.asIdeal) t.asIdeal ((p : ℕ) : O)).mpr hp
  have h2 := h1.map e
  rw [map_natCast] at h2
  exact h2

theorem eq_closedPoint_of_mem_support
    {O : Type u} [CommRing O] [IsLocalRing O] {p : ℕ}
    (h𝔪 : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {X : Scheme.{u}} (σ : Spec (CommRingCat.of O) ⟶ X)
    (J J' : X.IdealSheafData)
    (hprod : ∀ U : X.affineOpens, (J * J').ideal U = Ideal.span {((p : ℕ) : Γ(X, U))})
    (t : Spec (CommRingCat.of O)) (ht : σ.base t ∈ J.support) : t = IsLocalRing.closedPoint O := by
  classical
  by_contra hne

  have hp : ((p : ℕ) : O) ∉ t.asIdeal := by
    intro hp
    apply hne
    have hle : IsLocalRing.maximalIdeal O ≤ t.asIdeal := by
      rw [h𝔪, Ideal.span_singleton_le_iff_mem]; exact hp
    have heq : t.asIdeal = IsLocalRing.maximalIdeal O :=
      ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le t.isPrime.ne_top hle).symm
    exact PrimeSpectrum.ext heq

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (σ.base t)) isOpen_univ
  have hpJ : ((p : ℕ) : Γ(X, U)) ∈ J.ideal ⟨U, hU⟩ := by
    have h1 : ((p : ℕ) : Γ(X, U)) ∈ (J * J').ideal ⟨U, hU⟩ := by
      rw [hprod]; exact Ideal.mem_span_singleton_self _
    rw [Scheme.IdealSheafData.ideal_mul] at h1
    exact Ideal.mul_le_left h1
  have hz : σ.base t ∉ X.basicOpen ((p : ℕ) : Γ(X, U)) :=
    (X.mem_zeroLocus_iff _ _).mp ((Scheme.IdealSheafData.mem_support_iff_of_mem (I := J) (U := ⟨U, hU⟩) hxU).mp ht)
      _ hpJ
  have hnu : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (σ.base t)) := by
    intro hu
    apply hz
    rw [X.mem_basicOpen _ _ hxU, map_natCast]
    exact hu

  apply hnu
  have hu' := isUnit_natCast_stalk_of_not_mem t hp
  rw [← map_natCast (σ.stalkMap t).hom p] at hu'
  exact (isUnit_map_iff (σ.stalkMap t).hom _).mp hu'

theorem opens_eq_top_of_closedPoint_mem {O : Type u} [CommRing O] [IsLocalRing O]
    (W : (Spec (CommRingCat.of O)).Opens) (hW : IsLocalRing.closedPoint O ∈ W) : W = ⊤ := by
  ext t
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact (IsLocalRing.specializes_closedPoint t).mem_open W.isOpen hW

theorem mem_map_germ_ker_of_stalkMap_eq_zero
    {O : Type u} [CommRing O] [IsLocalRing O]
    {X : Scheme.{u}} (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ]
    (U : X.affineOpens) (hU : σ.base (IsLocalRing.closedPoint O) ∈ (U : X.Opens))
    (a : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint O)))
    (ha : (σ.stalkMap (IsLocalRing.closedPoint O)).hom a = 0) :
    a ∈ Ideal.map (X.presheaf.germ (U : X.Opens) (σ.base (IsLocalRing.closedPoint O)) hU).hom (σ.ker.ideal U) := by
  classical

  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.germ_exist (x := σ.base (IsLocalRing.closedPoint O)) a
  set t₀ := IsLocalRing.closedPoint O
  set x₀ : X := σ.base t₀
  obtain ⟨r, hrV, hxr⟩ := U.2.exists_basicOpen_le ⟨x₀, hxV⟩ hU
  let D : X.affineOpens := X.affineBasicOpen r
  have hxD : x₀ ∈ (D : X.Opens) := hxr
  let s' : Γ(X, D) := (X.presheaf.map (homOfLE hrV).op).hom s
  have hss' : (X.presheaf.germ (D : X.Opens) x₀ hxD).hom s' = (X.presheaf.germ V x₀ hxV).hom s :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hrV) x₀ hxD s
  rw [← hss'] at ha ⊢

  rw [Scheme.Hom.germ_stalkMap_apply σ (D : X.Opens) t₀ hxD s'] at ha
  rw [← map_zero ((Spec (CommRingCat.of O)).presheaf.germ (σ ⁻¹ᵁ (D : X.Opens)) t₀ hxD).hom] at ha
  obtain ⟨W, hW, iU, iV, hWeq⟩ := TopCat.Presheaf.germ_eq (Spec (CommRingCat.of O)).presheaf t₀ hxD hxD _ _ ha
  rw [map_zero] at hWeq
  have hWtop : W = ⊤ := opens_eq_top_of_closedPoint_mem W hW
  have hDtop : σ ⁻¹ᵁ (D : X.Opens) = ⊤ := opens_eq_top_of_closedPoint_mem _ hxD
  have hWD : W = σ ⁻¹ᵁ (D : X.Opens) := hWtop.trans hDtop.symm
  subst hWD
  have hiU : iU = 𝟙 _ := Subsingleton.elim _ _
  rw [hiU, op_id, CategoryTheory.Functor.map_id] at hWeq
  have hs'ker : s' ∈ σ.ker.ideal D := by
    rw [Scheme.Hom.ker_apply]
    exact hWeq

  have hgerm : (X.presheaf.germ (D : X.Opens) x₀ hxD).hom.comp (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      (X.presheaf.germ (U : X.Opens) x₀ hU).hom := by
    ext b
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le r)) x₀ hxD b
  rw [← hgerm, ← Ideal.map_map]
  apply Ideal.mem_map_of_mem
  erw [Scheme.IdealSheafData.map_ideal_basicOpen]
  exact hs'ker

theorem maximalIdeal_stalk_closedPoint_eq {O : Type u} [CommRing O] [IsLocalRing O] {p : ℕ}
    (h𝔪 : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of O)).presheaf.stalk (IsLocalRing.closedPoint O)) =
      Ideal.span {((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk (IsLocalRing.closedPoint O))} := by
  classical
  set t₀ := IsLocalRing.closedPoint O

  let e₁ : O ≃ₐ[O] Localization.AtPrime t₀.asIdeal :=
    IsLocalization.atUnits O t₀.asIdeal.primeCompl (fun x hx => by
      change x ∉ IsLocalRing.maximalIdeal O at hx
      simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx)
  let e : O ≃+* (Spec (CommRingCat.of O)).presheaf.stalk t₀ :=
    e₁.toRingEquiv.trans (StructureSheaf.stalkIso O t₀).toRingEquiv
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using (isLocalHom_equiv e).1 a ha⟩
  have h := map_maximalIdeal_of_surjective e.toRingHom e.surjective
  rw [← h, h𝔪, Ideal.map_span, Set.image_singleton]
  simp

theorem map_germ_ker_sup_eq_maximalIdeal
    {O : Type u} [CommRing O] [IsLocalRing O] {p : ℕ}
    (h𝔪 : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {X : Scheme.{u}} (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ]
    (J J' : X.IdealSheafData)
    (hprod : ∀ U : X.affineOpens, (J * J').ideal U = Ideal.span {((p : ℕ) : Γ(X, U))})
    (x₁ : X) (hx₁ : σ.base (IsLocalRing.closedPoint O) = x₁)
    (hJ' : x₁ ∉ J'.support) (hJ : x₁ ∈ J.support)
    (U : X.affineOpens) (hU : x₁ ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x₁ hU).hom (σ.ker.ideal U ⊔ J.ideal U) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x₁) := by
  classical
  subst hx₁
  set t₀ := IsLocalRing.closedPoint O
  set x₀ : X := σ.base t₀
  set g := (X.presheaf.germ (U : X.Opens) x₀ hU).hom with hg
  set ψ := (σ.stalkMap t₀).hom with hψ
  have hsurj : Function.Surjective ψ := σ.stalkMap_surjective t₀

  have aux : ∀ I : X.IdealSheafData, x₀ ∈ I.support → Ideal.map g (I.ideal U) ≤ IsLocalRing.maximalIdeal _ := by
    intro I hI
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hU).mp hI
    exact (X.mem_zeroLocus_iff _ _).mp hz f hf ((X.mem_basicOpen f x₀ hU).mpr hu)
  apply le_antisymm
  · rw [Ideal.map_sup, sup_le_iff]
    refine ⟨aux σ.ker ?_, aux J hJ⟩
    show x₀ ∈ ((σ.ker).support : Set X)
    rw [support_ker_eq_range]; exact ⟨t₀, rfl⟩
  · intro m hm

    have hA : Ideal.map ψ (Ideal.map g (J.ideal U)) = IsLocalRing.maximalIdeal _ := by

      have hJ'top : Ideal.map ψ (Ideal.map g (J'.ideal U)) = ⊤ := by
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := J') (U := U) hU, X.mem_zeroLocus_iff] at hJ'
        push_neg at hJ'
        obtain ⟨f, hf, hxf⟩ := hJ'
        apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem ψ (Ideal.mem_map_of_mem g hf))
        exact ((X.mem_basicOpen f x₀ hU).mp hxf).map ψ

      have hJJ' : Ideal.map ψ (Ideal.map g (J.ideal U)) * Ideal.map ψ (Ideal.map g (J'.ideal U)) =
          Ideal.span {((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk t₀)} := by
        rw [← Ideal.map_mul, ← Ideal.map_mul]
        have hmul : J.ideal U * J'.ideal U = (J * J').ideal U := by
          rw [Scheme.IdealSheafData.ideal_mul]; rfl
        rw [hmul, hprod U, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_span, Set.image_singleton,
          map_natCast]
      rw [hJ'top, Ideal.mul_top] at hJJ'
      rw [hJJ', maximalIdeal_stalk_closedPoint_eq h𝔪]
    have hψm : ψ m ∈ Ideal.map ψ (Ideal.map g (J.ideal U)) := by
      rw [hA]
      have hle : Ideal.map ψ (IsLocalRing.maximalIdeal _) ≤ IsLocalRing.maximalIdeal _ :=
        ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mp (inferInstance : IsLocalHom ψ)
      exact hle (Ideal.mem_map_of_mem ψ hm)
    obtain ⟨j, hj, hjm⟩ := (Ideal.mem_map_iff_of_surjective ψ hsurj).mp hψm
    have hB : m - j ∈ Ideal.map g (σ.ker.ideal U) :=
      mem_map_germ_ker_of_stalkMap_eq_zero σ U hU (m - j) (by rw [map_sub, hjm, sub_self])
    have hmj : m = (m - j) + j := by ring
    rw [hmj, Ideal.map_sup]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hB) (Ideal.mem_sup_right hj)

end AlgebraicGeometry.S1Y

open AlgebraicGeometry.S1Y in
theorem solution
    {O : Type u} [CommRing O] [IsLocalRing O] {p : ℕ}
    (h𝔪 : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {X : Scheme.{u}} (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ] (hker : σ.ker.IsInvertible)
    (J J' : X.IdealSheafData) [IsIntegral J.subscheme]
    (hprod : ∀ U : X.affineOpens, (J * J').ideal U = Ideal.span {((p : ℕ) : Γ(X, U))})
    (hJ' : σ.base (IsLocalRing.closedPoint O) ∉ J'.support)
    (hne : ∃ x ∈ J.support, x ∉ Set.range σ.base)
    {k : Type u} [Field k] (y : J.subscheme ⟶ Spec (CommRingCat.of k))
    (hrat : ∃ s : Spec (CommRingCat.of k) ⟶ J.subscheme,
      s ≫ y = 𝟙 _ ∧ σ.base (IsLocalRing.closedPoint O) ∈ Set.range (s ≫ J.subschemeι).base) :
    (σ.ker.comap J.subschemeι).IsInvertible ∧
      IsFinite ((σ.ker.comap J.subschemeι).subschemeι ≫ y) ∧
      ∀ q : Spec (CommRingCat.of k), ((σ.ker.comap J.subschemeι).subschemeι ≫ y).finrank q = 1 := by
  classical

  obtain ⟨s, hsy, t₀, ht₀⟩ := hrat
  set x₀ : X := σ.base (IsLocalRing.closedPoint O) with hx₀
  set w₀ : J.subscheme := s.base t₀ with hw₀
  have hιw₀ : J.subschemeι.base w₀ = x₀ := by
    rw [← ht₀]; rfl
  have hx₀J : x₀ ∈ J.support := by
    show x₀ ∈ (J.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w₀, hιw₀⟩

  have hinv : (σ.ker.comap J.subschemeι).IsInvertible := by
    obtain ⟨η, hηJ, hησ⟩ := hne
    refine isInvertible_comap_subschemeι_of_isIntegral hker hηJ ?_
    intro hη
    have : η ∈ ((σ.ker).support : Set X) := hη
    rw [support_ker_eq_range] at this
    exact hησ this

  have hsupp : (((σ.ker.comap J.subschemeι).support : Set J.subscheme)) = Set.range ![w₀] := by
    ext w
    rw [SetLike.mem_coe, mem_support_comap_iff]
    constructor
    · intro hw
      have hw' : J.subschemeι w ∈ ((σ.ker).support : Set X) := hw
      rw [support_ker_eq_range] at hw'
      obtain ⟨t, ht⟩ := hw'
      have hwJ : J.subschemeι w ∈ J.support := by
        show J.subschemeι w ∈ (J.support : Set X)
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩
      have htc : t = IsLocalRing.closedPoint O :=
        eq_closedPoint_of_mem_support h𝔪 σ J J' hprod t (ht ▸ hwJ)
      refine ⟨0, ?_⟩
      apply J.subschemeι.isClosedEmbedding.injective
      change J.subschemeι.base w₀ = J.subschemeι.base w
      rw [hιw₀, ← ht, htc]
    · rintro ⟨i, rfl⟩
      have hi : (![w₀] : Fin 1 → J.subscheme) i = w₀ := by fin_cases i; rfl
      rw [hi]
      show J.subschemeι w₀ ∈ ((σ.ker).support : Set X)
      rw [support_ker_eq_range]
      exact ⟨IsLocalRing.closedPoint O, hιw₀.symm⟩

  have hmax : ∀ i : Fin 1, ∃ (U : (J.subscheme).affineOpens) (hU : (![w₀] : Fin 1 → J.subscheme) i ∈ (U : (J.subscheme).Opens)),
      Ideal.map ((J.subscheme).presheaf.germ (U : (J.subscheme).Opens) ((![w₀] : Fin 1 → J.subscheme) i) hU).hom
          ((σ.ker.comap J.subschemeι).ideal U) =
        IsLocalRing.maximalIdeal ((J.subscheme).presheaf.stalk ((![w₀] : Fin 1 → J.subscheme) i)) := by
    intro i
    have hi : (![w₀] : Fin 1 → J.subscheme) i = w₀ := by fin_cases i; rfl
    rw [hi]

    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
    have hU' : J.subschemeι w₀ ∈ (U : Set X) := by
      change J.subschemeι.base w₀ ∈ (U : Set X); rw [hιw₀]; exact hxU
    refine ⟨⟨J.subschemeι ⁻¹ᵁ U, hU.preimage _⟩, hU', ?_⟩
    apply map_germ_comap_eq_maximalIdeal σ.ker J w₀ ⟨U, hU⟩ hU'
    have e : σ.base (IsLocalRing.closedPoint O) = J.subschemeι w₀ := hιw₀.symm
    exact map_germ_ker_sup_eq_maximalIdeal h𝔪 σ J J' hprod (J.subschemeι w₀) e (e ▸ hJ') (e ▸ hx₀J) ⟨U, hU⟩ hU'
  have hrat' : ∀ i : Fin 1, ∃ s' : Spec (CommRingCat.of k) ⟶ J.subscheme,
      s' ≫ y = 𝟙 _ ∧ (![w₀] : Fin 1 → J.subscheme) i ∈ Set.range s'.base := by
    intro i
    have hi : (![w₀] : Fin 1 → J.subscheme) i = w₀ := by fin_cases i; rfl
    refine ⟨s, hsy, ?_⟩
    rw [hi]
    exact ⟨t₀, rfl⟩
  obtain ⟨hfin, hdeg⟩ :=
    Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
      y (σ.ker.comap J.subschemeι) ![w₀] (fun i j _ => Subsingleton.elim i j) hsupp hmax hrat'
  exact ⟨hinv, hfin, hdeg⟩

end S_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast (solution)
