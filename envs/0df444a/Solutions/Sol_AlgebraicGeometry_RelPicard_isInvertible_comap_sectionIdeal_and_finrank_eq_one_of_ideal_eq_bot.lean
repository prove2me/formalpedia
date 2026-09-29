-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/27516238-6933-52ff-9ffe-ffc5c855571d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso IsClosedImmersion.isIso_lift SmoothOfRelativeDimension IsClosedImmersion.of_comp Scheme.Hom exists_basicOpen_le_affine_inter Scheme.Hom.germ_stalkMap_apply IsFinite QuasiCompact Scheme.Hom.support_ker Spec Scheme Scheme.IdealSheafData.ker_fst_of_isClosedImmersion germ_injective_of_isIntegral Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion IsSeparated Scheme.mem_zeroLocus_iff IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.ker Scheme.Hom.isClosedEmbedding Scheme.Hom.ker_apply Scheme.Hom.app_eq_appLE Scheme.Hom.finrank_eq_one_of_isIso Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.IdealSheafData.ker_subschemeι_app Scheme.IdealSheafData Scheme.IdealSheafData.ideal_comap_of_le"
namespace SecDegS17
p2m_open "AlgebraicGeometry"

theorem map_germ_ideal_eq {X : Scheme.{u}} (I : X.IdealSheafData) {x : X} (V W : X.affineOpens)
    (hV : x ∈ (V : X.Opens)) (hW : x ∈ (W : X.Opens)) :
    Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom (I.ideal V) =
      Ideal.map (X.presheaf.germ (W : X.Opens) x hW).hom (I.ideal W) := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hV, hW⟩
  have key : ∀ (T : X.affineOpens) (hT : x ∈ (T : X.Opens))
      (hle : (X.affineBasicOpen f : X.Opens) ≤ (T : X.Opens)),
      Ideal.map (X.presheaf.germ (T : X.Opens) x hT).hom (I.ideal T) =
        Ideal.map (X.presheaf.germ (X.affineBasicOpen f : X.Opens) x hxf).hom
          (I.ideal (X.affineBasicOpen f)) := by
    intro T hT hle
    rw [← I.map_ideal (U := X.affineBasicOpen f) (V := T) hle, Ideal.map_map]
    congr 1
    rw [← TopCat.Presheaf.germ_res X.presheaf (homOfLE hle) x hxf, CommRingCat.hom_comp]
    rfl
  rw [key V hV (X.basicOpen_le f), key W hW]
  change X.basicOpen f ≤ (W : X.Opens)
  rw [hfg]
  exact X.basicOpen_le g

theorem ideal_eq_bot_of_basicOpen_eq {X : Scheme.{u}} (J : X.IdealSheafData) {V U : X.affineOpens}
    (hJV : J.ideal V = ⊥) (f : Γ(X, U)) (g : Γ(X, V)) (hfg : X.basicOpen f = X.basicOpen g) :
    J.ideal (X.affineBasicOpen f) = ⊥ := by
  have : X.affineBasicOpen f = X.affineBasicOpen g := Subtype.ext hfg
  rw [this, ← J.map_ideal_basicOpen V g, hJV, Ideal.map_bot]
  rfl

theorem map_mem_nonZeroDivisors_basicOpen {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    {g : Γ(X, U)} (hg : g ∈ nonZeroDivisors Γ(X, U)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f) := by
  letI := U.2.isLocalization_basicOpen f
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers f) (S := Γ(X, X.basicOpen f)) hg

theorem subschemeι_app_injective_of_ideal_eq_bot {X : Scheme.{u}} (J : X.IdealSheafData) (U : X.affineOpens)
    (hJ : J.ideal U = ⊥) : Function.Injective (J.subschemeι.app (U : X.Opens)).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : a ∈ RingHom.ker (J.subschemeι.app (U : X.Opens)).hom := ha
  rwa [Scheme.IdealSheafData.ker_subschemeι_app, hJ, Ideal.mem_bot] at this

theorem map_mem_nonZeroDivisors_of_bijective {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Bijective φ) {g : A} (hg : g ∈ nonZeroDivisors A) : φ g ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  obtain ⟨a, rfl⟩ := hφ.2 b
  rw [← map_mul, ← map_zero φ] at hb
  rw [hφ.1 hb |> fun h => (mem_nonZeroDivisors_iff_right.mp hg a h), map_zero]

theorem isInvertible_comap_subschemeι {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible)
    (S : Set X) (hIS : ∀ x : X, x ∉ S → x ∉ I.support)
    (hJS : ∀ x ∈ S, ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ J.ideal V = ⊥) :
    (I.comap J.subschemeι).IsInvertible := by
  intro w
  set x : X := J.subschemeι w with hxdef
  by_cases hxS : x ∈ S
  ·
    obtain ⟨V, hxV, hJV⟩ := hJS x hxS
    obtain ⟨U₀, f₀, hxf₀, g₀, hg₀, hIg₀⟩ := hI x
    obtain ⟨f₁, g₁, hfg₁, hxf₁⟩ :=
      exists_basicOpen_le_affine_inter (X.affineBasicOpen f₀).2 V.2 x ⟨hxf₀, hxV⟩

    let D : X.affineOpens := X.affineBasicOpen f₁
    have hxD : x ∈ (D : X.Opens) := hxf₁
    have hDle : (D : X.Opens) ≤ X.affineBasicOpen f₀ := X.basicOpen_le f₁
    let g : Γ(X, D) := (X.presheaf.map (homOfLE hDle).op).hom g₀
    have hg : g ∈ nonZeroDivisors Γ(X, D) := map_mem_nonZeroDivisors_basicOpen _ f₁ hg₀
    have hIg : I.ideal D = Ideal.span {g} := by
      rw [← I.map_ideal_basicOpen (X.affineBasicOpen f₀) f₁, hIg₀, Ideal.map_span, Set.image_singleton]
      rfl
    have hJD : J.ideal D = ⊥ := ideal_eq_bot_of_basicOpen_eq J hJV f₁ g₁ hfg₁

    let E : (J.subscheme).affineOpens := ⟨J.subschemeι ⁻¹ᵁ (D : X.Opens), D.2.preimage J.subschemeι⟩
    have hwE : w ∈ (E : (J.subscheme).Opens) := hxD
    have happ : J.subschemeι.appLE (D : X.Opens) (E : (J.subscheme).Opens) le_rfl = J.subschemeι.app (D : X.Opens) :=
      (Scheme.Hom.app_eq_appLE _).symm
    let gW : Γ(J.subscheme, E) := (J.subschemeι.appLE (D : X.Opens) (E : (J.subscheme).Opens) le_rfl).hom g
    have hbij : Function.Bijective (J.subschemeι.appLE (D : X.Opens) (E : (J.subscheme).Opens) le_rfl).hom := by
      rw [happ]
      exact ⟨subschemeι_app_injective_of_ideal_eq_bot J D hJD, J.subschemeι_app_surjective D⟩
    have hgW : gW ∈ nonZeroDivisors Γ(J.subscheme, E) := map_mem_nonZeroDivisors_of_bijective _ hbij hg
    have hKE : (I.comap J.subschemeι).ideal E = Ideal.span {gW} := by
      rw [Scheme.IdealSheafData.ideal_comap_of_le I J.subschemeι D E le_rfl, hIg, Ideal.map_span,
        Set.image_singleton]
    refine ⟨E, 1, ?_, (J.subscheme.presheaf.map (homOfLE ((J.subscheme).basicOpen_le (1 : Γ(J.subscheme, E)))).op).hom gW,
      map_mem_nonZeroDivisors_basicOpen E 1 hgW, ?_⟩
    · rw [(J.subscheme).basicOpen_of_isUnit isUnit_one]; exact hwE
    · rw [← (I.comap J.subschemeι).map_ideal_basicOpen E 1, hKE, Ideal.map_span, Set.image_singleton]
      rfl
  ·
    have hxI : x ∉ I.support := hIS x hxS
    obtain ⟨U₀, f₀, hxf₀, -⟩ := hI x
    have hxU₀ : x ∈ (U₀ : X.Opens) := X.basicOpen_le f₀ hxf₀
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U₀) hxU₀, Scheme.mem_zeroLocus_iff] at hxI
    push Not at hxI
    obtain ⟨f, hfI, hxf⟩ := hxI
    let D : X.affineOpens := X.affineBasicOpen f
    have hxD : x ∈ (D : X.Opens) := hxf
    have hID : I.ideal D = ⊤ := by
      rw [← I.map_ideal_basicOpen U₀ f]
      apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hfI)
      letI := U₀.2.isLocalization_basicOpen f
      exact IsLocalization.map_units (M := Submonoid.powers f) Γ(X, X.basicOpen f) ⟨f, Submonoid.mem_powers f⟩
    let E : (J.subscheme).affineOpens := ⟨J.subschemeι ⁻¹ᵁ (D : X.Opens), D.2.preimage J.subschemeι⟩
    have hwE : w ∈ (E : (J.subscheme).Opens) := hxD
    have hKE : (I.comap J.subschemeι).ideal E = ⊤ := by
      rw [Scheme.IdealSheafData.ideal_comap_of_le I J.subschemeι D E le_rfl, hID, Ideal.map_top]
    refine ⟨E, 1, ?_, 1, one_mem _, ?_⟩
    · rw [(J.subscheme).basicOpen_of_isUnit isUnit_one]; exact hwE
    · rw [← (I.comap J.subschemeι).map_ideal_basicOpen E 1, hKE, Ideal.map_top, Ideal.span_singleton_one]
      rfl

theorem le_ker_of_ideal_eq_bot {X : Scheme.{u}} {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ X)
    [QuasiCompact s] (J : X.IdealSheafData) (V : X.affineOpens)
    (hsV : Set.range s ⊆ ((V : X.Opens) : Set X)) (hJV : J.ideal V = ⊥) : J ≤ s.ker := by
  intro U a ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  rcases TopologicalSpace.Opens.eq_bot_or_top (s ⁻¹ᵁ (U : X.Opens)) with h | h
  · haveI : Subsingleton Γ(Spec (CommRingCat.of k), s ⁻¹ᵁ (U : X.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal
        (TopCat.Sheaf.isTerminalOfEqEmpty (Spec (CommRingCat.of k)).sheaf h)
    exact Subsingleton.elim _ _
  · let pt : Spec (CommRingCat.of k) := default
    have hpt : pt ∈ s ⁻¹ᵁ (U : X.Opens) := by rw [h]; trivial
    have hx : s pt ∈ (U : X.Opens) := hpt
    have hxV : s pt ∈ (V : X.Opens) := hsV ⟨pt, rfl⟩
    apply germ_injective_of_isIntegral _ pt hpt
    rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply s (U : X.Opens) pt hx]
    have h0 : (X.presheaf.germ (U : X.Opens) (s pt) hx).hom a = 0 := by
      have hmem : (X.presheaf.germ (U : X.Opens) (s pt) hx).hom a ∈
          Ideal.map (X.presheaf.germ (U : X.Opens) (s pt) hx).hom (J.ideal U) := Ideal.mem_map_of_mem _ ha
      rw [map_germ_ideal_eq J U V hx hxV, hJV, Ideal.map_bot, Ideal.mem_bot] at hmem
      exact hmem
    change (s.stalkMap pt).hom ((X.presheaf.germ (U : X.Opens) (s pt) hx).hom a) = 0
    rw [h0, map_zero]

end AlgebraicGeometry.SecDegS17

open AlgebraicGeometry.SecDegS17 in

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hσ : Set.range σ.1 ⊆ (U : Set C))
    {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (J : (pullback c t).IdealSheafData)
    (hJ : ∃ V : (pullback c t).affineOpens,
      Set.range (rigSection c t σ) ⊆ ((V : (pullback c t).Opens) : Set ↥(pullback c t)) ∧ J.ideal V = ⊥) :
    ((sectionIdeal c σ t).comap J.subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) ∧
      ∀ q : Spec (CommRingCat.of k),
        (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t).finrank q = 1 := by

  have hs_snd : rigSection c t σ ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (rigSection c t σ) := by
    have : IsClosedImmersion (rigSection c t σ ≫ pullback.snd c t) := by rw [hs_snd]; infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t σ) (pullback.snd c t)
  have hI : (sectionIdeal c σ t).IsInvertible := isInvertible_sectionIdeal_of_range_subset c σ U hσ t
  have hIker : sectionIdeal c σ t = (rigSection c t σ).ker := rfl
  obtain ⟨V, hsV, hJV⟩ := hJ
  have hsupp : ((sectionIdeal c σ t).support : Set ↥(pullback c t)) = Set.range (rigSection c t σ) := by
    rw [hIker, Scheme.Hom.support_ker, (Scheme.Hom.isClosedEmbedding (rigSection c t σ)).isClosed_range.closure_eq]
  refine ⟨?_, ?_⟩
  ·
    refine isInvertible_comap_subschemeι hI (Set.range (rigSection c t σ)) (fun x hx h => hx ?_)
      (fun x hx => ⟨V, hsV hx, hJV⟩)
    have h' : x ∈ ((sectionIdeal c σ t).support : Set ↥(pullback c t)) := h
    rwa [hsupp] at h'
  ·
    have hle : J ≤ (rigSection c t σ).ker := le_ker_of_ideal_eq_bot (rigSection c t σ) J V hsV hJV
    let φ : Spec (CommRingCat.of k) ⟶ J.subscheme :=
      IsClosedImmersion.lift J.subschemeι (rigSection c t σ) (by rwa [Scheme.IdealSheafData.ker_subschemeι])
    have hφ : φ ≫ J.subschemeι = rigSection c t σ := IsClosedImmersion.lift_fac _ _ _
    let ψ : Spec (CommRingCat.of k) ⟶ pullback J.subschemeι (rigSection c t σ) :=
      pullback.lift φ (𝟙 _) (by rw [hφ, Category.id_comp])
    have hψsnd : ψ ≫ pullback.snd J.subschemeι (rigSection c t σ) = 𝟙 _ := pullback.lift_snd _ _ _
    have hψfst : ψ ≫ pullback.fst J.subschemeι (rigSection c t σ) = φ := pullback.lift_fst _ _ _
    haveI : IsIso (pullback.snd J.subschemeι (rigSection c t σ)) := by
      refine ⟨⟨ψ, ?_, hψsnd⟩⟩
      rw [← cancel_mono (pullback.snd J.subschemeι (rigSection c t σ)), Category.assoc, hψsnd,
        Category.comp_id, Category.id_comp]
    haveI : IsIso ψ := by
      have : ψ = inv (pullback.snd J.subschemeι (rigSection c t σ)) := by
        rw [← cancel_mono (pullback.snd J.subschemeι (rigSection c t σ)), hψsnd, IsIso.inv_hom_id]
      rw [this]; infer_instance
    haveI : IsClosedImmersion φ := by
      have : IsClosedImmersion (φ ≫ J.subschemeι) := by rw [hφ]; infer_instance
      exact IsClosedImmersion.of_comp φ J.subschemeι
    set K := (sectionIdeal c σ t).comap J.subschemeι with hKdef
    have hK : K = φ.ker := by
      rw [hKdef, hIker, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (rigSection c t σ) J.subschemeι,
        ← hψfst, Scheme.Hom.ker_comp_of_isIso]
    have hkers : Scheme.Hom.ker K.subschemeι = Scheme.Hom.ker φ := by
      rw [Scheme.IdealSheafData.ker_subschemeι, hK]
    haveI : IsIso (IsClosedImmersion.lift K.subschemeι φ hkers.le) :=
      IsClosedImmersion.isIso_lift K.subschemeι φ hkers
    have he : IsClosedImmersion.lift K.subschemeι φ hkers.le ≫ K.subschemeι = φ := IsClosedImmersion.lift_fac _ _ _
    have hcomp : K.subschemeι ≫ J.subschemeι ≫ pullback.snd c t = inv (IsClosedImmersion.lift K.subschemeι φ hkers.le) := by
      rw [← cancel_epi (IsClosedImmersion.lift K.subschemeι φ hkers.le), ← Category.assoc, he, ← Category.assoc, hφ,
        hs_snd, IsIso.hom_inv_id]
    rw [hcomp]
    exact ⟨inferInstance, fun q => by rw [Scheme.Hom.finrank_eq_one_of_isIso]; rfl⟩

end S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot (solution)
