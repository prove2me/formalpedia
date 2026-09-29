-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.maximalIdeal_stalk_eq_span_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a5f953c5-49a0-56cd-8936-30c6715f9cc6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes.AlgebraicGeometry Topology"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.mem_basicOpen Scheme.basicOpen_res Scheme.IdealSheafData.radical_ideal Scheme.IdealSheafData.map_bot Scheme.ker_of_isAffine Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth Scheme.IdealSheafData.vanishingIdeal Scheme.IdealSheafData.map_vanishingIdeal IsClosedImmersion.spec_of_surjective Scheme.IdealSheafData.vanishingIdeal_top IsClosedImmersion IsReduced Scheme.preimage_basicOpen_top Scheme.nilradical_eq_bot Scheme.mem_basicOpen_top Scheme.IdealSheafData.ofIdealTop Scheme.IdealSheafData.vanishingIdeal_support basicOpen_eq_of_affine Scheme.IdealSheafData.ofIdealTop_ideal geometrically Scheme.IdealSheafData Scheme.ΓSpecIso Smooth.isReduced_of_isReduced_of_isLocallyNoetherian"
p2m_open "AlgebraicGeometry"

open IsLocalRing TopologicalSpace

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res IdealSheafData.radical_ideal IdealSheafData.map_bot ker_of_isAffine IdealSheafData.coe_support_vanishingIdeal Hom mk Γ ΓSpecIso_inv_naturality IdealSheafData.vanishingIdeal IdealSheafData.map_vanishingIdeal IdealSheafData.vanishingIdeal_top basicOpen preimage_basicOpen_top nilradical_eq_bot isBasis_affineOpens mem_basicOpen_top residue le_iff_specializes IdealSheafData.ofIdealTop IdealSheafData.vanishingIdeal_support IdealSheafData.ofIdealTop_ideal IdealSheafData ΓSpecIso" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image isOpenEmbedding injective mk appTop preimage_basicOpen_top continuous ker comp_apply" end Scheme.Hom
namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem _root_.AlgebraicGeometry.Scheme.Hom.radical_ker_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] : f.ker.radical = f.ker := by
  have hk : f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f.base), isClosed_closure⟩ := by
    rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := X), ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    congr 1
    ext1
    simp [Set.image_univ]
  rw [hk]
  set Z : Closeds Y := ⟨closure (Set.range f.base), isClosed_closure⟩
  have h : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
    Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  conv_rhs => rw [← h]
  exact Scheme.IdealSheafData.vanishingIdeal_support.symm

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.radical_ker_of_isReduced"
namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res IdealSheafData.radical_ideal IdealSheafData.map_bot ker_of_isAffine IdealSheafData.coe_support_vanishingIdeal Hom mk Γ ΓSpecIso_inv_naturality IdealSheafData.vanishingIdeal IdealSheafData.map_vanishingIdeal IdealSheafData.vanishingIdeal_top basicOpen preimage_basicOpen_top nilradical_eq_bot isBasis_affineOpens mem_basicOpen_top residue le_iff_specializes IdealSheafData.ofIdealTop IdealSheafData.vanishingIdeal_support IdealSheafData.ofIdealTop_ideal IdealSheafData ΓSpecIso" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical radical_ideal map_bot coe_support_vanishingIdeal mk map subscheme vanishingIdeal ker_fst_of_isClosedImmersion map_vanishingIdeal ideal vanishingIdeal_top comap ofIdealTop support vanishingIdeal_support ofIdealTop_ideal comap_ofIdealTop" end Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

theorem Scheme.IdealSheafData.radical_comap_ker_of_smooth' {Z B Y : Scheme.{u}} (i : Z ⟶ B) [IsClosedImmersion i]
    [IsReduced Z] [IsLocallyNoetherian Z] (f : Y ⟶ B) [Smooth f] :
    (i.ker.comap f).radical = i.ker.comap f := by
  rw [← ker_fst_of_isClosedImmersion]
  haveI : Smooth (Limits.pullback.snd f i) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsReduced (Limits.pullback f i) := Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (Limits.pullback.snd f i)
  exact (Limits.pullback.fst f i).radical_ker_of_isReduced

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res IdealSheafData.radical_ideal IdealSheafData.map_bot ker_of_isAffine IdealSheafData.coe_support_vanishingIdeal Hom mk Γ ΓSpecIso_inv_naturality IdealSheafData.vanishingIdeal IdealSheafData.map_vanishingIdeal IdealSheafData.vanishingIdeal_top basicOpen preimage_basicOpen_top nilradical_eq_bot isBasis_affineOpens mem_basicOpen_top residue le_iff_specializes IdealSheafData.ofIdealTop IdealSheafData.vanishingIdeal_support IdealSheafData.ofIdealTop_ideal IdealSheafData ΓSpecIso" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.ker_Spec_map_quotient_mk' {O : Type u} [CommRing O] (J : Ideal O) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker =
      Scheme.IdealSheafData.ofIdealTop (J.map (Scheme.ΓSpecIso (.of O)).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  have h : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop =
      (Scheme.ΓSpecIso (.of O)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (.of (O ⧸ J))).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rw [h]
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of (O ⧸ J))).inv.hom := by
    intro a b hab
    have := congrArg (Scheme.ΓSpecIso (.of (O ⧸ J))).hom.hom hab
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id] at this
    simpa using this

  have hmc : J.map (Scheme.ΓSpecIso (.of O)).inv.hom = J.comap (Scheme.ΓSpecIso (.of O)).hom.hom := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, ← CommRingCat.comp_apply, Iso.inv_hom_id]
      simpa using hx
    · intro x hx
      rw [Ideal.mem_comap] at hx
      have : x = (Scheme.ΓSpecIso (.of O)).inv.hom ((Scheme.ΓSpecIso (.of O)).hom.hom x) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; simp
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
  rw [hmc]
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_comap, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  constructor
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hinj
    rw [hx, map_zero]
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

theorem Scheme.IdealSheafData.radical_ofIdealTop_span_appTop_of_smooth {O : Type u} [CommRing O] (ϖ : O)
    [_root_.IsReduced (O ⧸ Ideal.span {ϖ})] [IsNoetherianRing (O ⧸ Ideal.span {ϖ})]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of O)) [Smooth f] :
    (ofIdealTop (Ideal.span {f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv ϖ)})).radical =
      ofIdealTop (Ideal.span {f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv ϖ)}) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have h := radical_comap_ker_of_smooth' (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ})))) f
  rw [Scheme.ker_Spec_map_quotient_mk', comap_ofIdealTop, Ideal.map_map, Ideal.map_span, Set.image_singleton] at h
  simpa using h

p2m_open_scoped "AlgebraicGeometry.PrimeSpectrum" in

theorem PrimeSpectrum.mem_asIdeal_iff_eq_closedPoint {R : Type u} [CommRing R] [IsLocalRing R] (ϖ : R)
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (x : PrimeSpectrum R) : ϖ ∈ x.asIdeal ↔ x = closedPoint R := by
  constructor
  · intro h
    have hle : maximalIdeal R ≤ x.asIdeal := by rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact PrimeSpectrum.ext ((maximalIdeal.isMaximal R).eq_of_le x.isPrime.ne_top hle).symm
  · rintro rfl
    show ϖ ∈ maximalIdeal R
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

end AlgebraicGeometry

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    IsLocalRing.maximalIdeal (T.presheaf.stalk η) =
      Ideal.span {(T.presheaf.germ ⊤ η trivial).hom ((t.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))} := by
  classical

  set τ : Γ(T, ⊤) := (t.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ) with hτ

  have hpre : T.basicOpen τ = t ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ) :=
    (Scheme.preimage_basicOpen_top t ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)).symm
  have hL0 : ∀ y : T, t.base y = IsLocalRing.closedPoint R ↔ y ∉ T.basicOpen τ := fun y => by
    have h1 : y ∈ T.basicOpen τ ↔ ϖ ∉ (t.base y).asIdeal := by
      rw [hpre]
      change t.base y ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ) ↔ _
      rw [basicOpen_eq_of_affine]
      exact Iff.rfl
    rw [h1, not_not]
    exact (PrimeSpectrum.mem_asIdeal_iff_eq_closedPoint ϖ hϖ (t.base y)).symm

  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  let 𝔭 := hU.primeIdealOf ⟨η, hηU⟩
  letI := T.presheaf.algebra_section_stalk (⟨η, hηU⟩ : U)
  haveI hloc : IsLocalization.AtPrime (T.presheaf.stalk η) 𝔭.asIdeal := hU.isLocalization_stalk ⟨η, hηU⟩
  set τU : Γ(T, U) := (T.presheaf.map (homOfLE le_top).op).hom τ with hτU

  have hgerm : (T.presheaf.germ ⊤ η trivial).hom τ = algebraMap Γ(T, U) (T.presheaf.stalk η) τU := by
    change (T.presheaf.germ ⊤ η trivial).hom τ = (T.presheaf.germ U η hηU).hom τU
    conv_rhs => rw [hτU, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
  rw [hgerm, ← Set.image_singleton, ← Ideal.map_span]
  set I : Ideal Γ(T, U) := Ideal.span {τU} with hI

  haveI hmaxϖ : (Ideal.span {ϖ}).IsMaximal := hϖ ▸ IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI : _root_.IsReduced (R ⧸ Ideal.span {ϖ}) := inferInstance
  haveI : IsNoetherianRing (R ⧸ Ideal.span {ϖ}) := inferInstance
  have hradSheaf := Scheme.IdealSheafData.radical_ofIdealTop_span_appTop_of_smooth ϖ t
  have hIrad : I.radical = I := by
    have h := congrArg (fun J : T.IdealSheafData => J.ideal ⟨U, hU⟩) hradSheaf
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
      Set.image_singleton] at h
    exact h
  have hIArad : (I.map (algebraMap Γ(T, U) (T.presheaf.stalk η))).radical = I.map (algebraMap _ _) := by
    rw [← IsLocalization.map_radical 𝔭.asIdeal.primeCompl (T.presheaf.stalk η) I, hIrad]

  have hτU𝔭 : τU ∈ 𝔭.asIdeal := by
    have hη := (hL0 η).mp hηs
    rw [Scheme.mem_basicOpen_top, hgerm] at hη

    by_contra hn
    exact hη ((IsLocalization.AtPrime.isUnit_to_map_iff (T.presheaf.stalk η) 𝔭.asIdeal τU).mpr hn)
  have hIle : I.map (algebraMap Γ(T, U) (T.presheaf.stalk η)) ≤ IsLocalRing.maximalIdeal _ := by
    rw [hI, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (T.presheaf.stalk η) 𝔭.asIdeal τU).mpr hτU𝔭

  have hprime : ∀ 𝔮 : Ideal (T.presheaf.stalk η), 𝔮.IsPrime →
      I.map (algebraMap Γ(T, U) (T.presheaf.stalk η)) ≤ 𝔮 → 𝔮 = IsLocalRing.maximalIdeal _ := by
    intro 𝔮 h𝔮 hI𝔮
    let 𝔮₀ : Ideal Γ(T, U) := 𝔮.comap (algebraMap Γ(T, U) (T.presheaf.stalk η))
    haveI : 𝔮₀.IsPrime := Ideal.IsPrime.comap _
    let q : PrimeSpectrum Γ(T, U) := ⟨𝔮₀, inferInstance⟩

    let y : T := hU.fromSpec.base q
    have h𝔭η : hU.fromSpec.base 𝔭 = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩
    have hyU : y ∈ U := by
      have h := Set.mem_range_self (f := hU.fromSpec.base) q
      rw [hU.range_fromSpec] at h
      exact h
    have hq𝔭 : 𝔮₀ ≤ 𝔭.asIdeal := by
      intro b hb
      rw [Ideal.mem_comap] at hb
      have hb' : algebraMap Γ(T, U) (T.presheaf.stalk η) b ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk η) :=
        IsLocalRing.le_maximalIdeal h𝔮.ne_top hb
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (T.presheaf.stalk η) 𝔭.asIdeal b).mp hb'
    have hyη : y ⤳ η := by
      have h1 : q ⤳ 𝔭 := (PrimeSpectrum.le_iff_specializes q 𝔭).mp hq𝔭
      have h2 := h1.map hU.fromSpec.continuous
      rwa [h𝔭η] at h2

    have hτq : τU ∈ 𝔮₀ := by
      rw [Ideal.mem_comap]
      apply hI𝔮
      rw [hI, Ideal.map_span, Set.image_singleton]
      exact Ideal.mem_span_singleton_self _
    have hys : t.base y = IsLocalRing.closedPoint R := by
      rw [hL0]
      intro hyb
      have hyb' : y ∈ T.basicOpen τU := by
        rw [hτU, Scheme.basicOpen_res]
        exact ⟨hyU, hyb⟩
      letI := T.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
      haveI : IsLocalization.AtPrime (T.presheaf.stalk y) q.asIdeal := hU.isLocalization_stalk' q hyU
      rw [Scheme.mem_basicOpen T τU y hyU] at hyb'
      have := (IsLocalization.AtPrime.isUnit_to_map_iff (T.presheaf.stalk y) q.asIdeal τU).mp hyb'
      exact this hτq

    have hyeq : y = η := hgen y hyη hys
    have hq : q = 𝔭 := by
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [h𝔭η]
      exact hyeq
    have h𝔮₀ : 𝔮₀ = 𝔭.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    calc 𝔮 = 𝔮₀.map (algebraMap Γ(T, U) (T.presheaf.stalk η)) :=
          (IsLocalization.map_comap 𝔭.asIdeal.primeCompl (T.presheaf.stalk η) 𝔮).symm
      _ = IsLocalRing.maximalIdeal _ := by
          rw [h𝔮₀]; exact IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭.asIdeal (T.presheaf.stalk η)

  apply le_antisymm
  · rw [← hIArad, Ideal.radical_eq_sInf]
    exact le_sInf (fun J hJ => (hprime J hJ.2 hJ.1).ge)
  · exact hIle

end S_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes (solution)
