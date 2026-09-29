-- Prove2me | solution 1 for AlgebraicCurve.Place.forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/32ac8e6e-6c22-5375-a36a-e246233575eb

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Manifold ContDiff Topology
open Filter Set

namespace BadSet16

theorem top_le_iff {X : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ p ⁻¹ᵁ U ↔ p.base (IsLocalRing.closedPoint ℂ) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ _)
  · intro h
    rw [Scheme.preimage_eq_top_of_closedPoint_mem p h]

theorem val_ne_zero_iff {X : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (b : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ h) b) ≠ 0 ↔
      p.base (IsLocalRing.closedPoint ℂ) ∈ X.basicOpen b := by
  have hQ : p.base (IsLocalRing.closedPoint ℂ) ∈ U := (top_le_iff p U).1 h
  rw [Scheme.mem_basicOpen (hx := hQ)]
  have key := Scheme.germ_stalkClosedPointTo p U hQ
  have hk := congrArg (fun φ => φ.hom b) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hk
  have hval : (Scheme.stalkClosedPointTo p).hom ((X.presheaf.germ U _ hQ).hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ h) b) := by
    rw [hk]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE]
    rfl
  rw [← hval, ← isUnit_iff_ne_zero]
  exact (isUnit_map_iff (Scheme.stalkClosedPointTo p).hom _)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

theorem exists_chart_disc (v₀ : M) (S : Set M) (hS : IsOpen S) (hv₀ : v₀ ∈ S) :
    ∃ D : Set M, IsOpen D ∧ _root_.IsConnected D ∧ v₀ ∈ D ∧ D ⊆ S := by
  set e := extChartAt 𝓘(ℂ, ℂ) v₀ with he
  have h1 : e.target ∈ 𝓝 (e v₀) := extChartAt_target_mem_nhds v₀
  have h2 : e.symm ⁻¹' S ∈ 𝓝 (e v₀) := by
    apply (continuousAt_extChartAt_symm v₀).preimage_mem_nhds
    rw [extChartAt_to_inv]; exact hS.mem_nhds hv₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem h1 h2)
  have hBT : Metric.ball (e v₀) r ⊆ e.target := fun z hz => (hball hz).1
  refine ⟨e.symm '' Metric.ball (e v₀) r, ?_, ?_, ?_, ?_⟩
  · rw [e.symm_image_eq_source_inter_preimage hBT]
    exact isOpen_extChartAt_preimage' v₀ Metric.isOpen_ball
  · have hconn : _root_.IsConnected (Metric.ball (e v₀) r) :=
      ⟨⟨e v₀, Metric.mem_ball_self hr⟩, (convex_ball (e v₀) r).isPreconnected⟩
    exact hconn.image _ ((continuousOn_extChartAt_symm v₀).mono hBT)
  · exact ⟨e v₀, Metric.mem_ball_self hr, extChartAt_to_inv v₀⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hball hz).2

variable [IsManifold 𝓘(ℂ, ℂ) ω M]

theorem analyticAt_extChartAt {S : Set M} (hS : IsOpen S) (G : M → ℂ)
    (hG : ∀ v ∈ S, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v))
    {x : M} (hx : x ∈ S) :
    AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x) := by
  set e := extChartAt 𝓘(ℂ, ℂ) x with he
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have h1 : e.target ∈ 𝓝 (e x) := extChartAt_target_mem_nhds x
  have h2 : e.symm ⁻¹' S ∈ 𝓝 (e x) := by
    apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
    rw [extChartAt_to_inv]; exact hS.mem_nhds hx
  filter_upwards [h1, h2] with z hz1 hz2
  have hvS : e.symm z ∈ S := hz2
  set e' := extChartAt 𝓘(ℂ, ℂ) (e.symm z) with he'
  have hzc : ContinuousAt e.symm z := continuousAt_extChartAt_symm'' hz1
  have hev : (fun z' : ℂ => G (e.symm z')) =ᶠ[𝓝 z]
      ((fun u : ℂ => G (e'.symm u)) ∘ (e' ∘ e.symm)) := by
    have hpre : e.symm ⁻¹' e'.source ∈ 𝓝 z :=
      hzc.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (e.symm z))
    filter_upwards [hpre] with z' hz'
    simp only [Function.comp_apply]
    rw [e'.left_inv hz']
  refine (Filter.EventuallyEq.differentiableAt_iff hev).2 ?_
  have hd1 : DifferentiableAt ℂ (fun u : ℂ => G (e'.symm u)) ((e' ∘ e.symm) z) := hG (e.symm z) hvS
  have hd2 : DifferentiableAt ℂ (e' ∘ e.symm) z := by
    have hmem : z ∈ (e.symm ≫ e').source := by
      rw [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨hz1, mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) (e.symm z)⟩
    have hcd := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) (e.symm z) x hmem
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at hcd
    exact hcd.differentiableAt (by simp)
  exact hd1.comp z hd2

end BadSet16

open BadSet16 in
theorem solution
    (F : Type) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pY] [LocallyOfFiniteType pY]
    (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
    (hw : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (φ : Γ(Y, U)),
      IsOpen {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} ∧
      ∃ G : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
          G v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) ∧
        ∀ v : Place ℂ F, ⊤ ≤ (w v).1 ⁻¹ᵁ U →
          DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
            (extChartAt 𝓘(ℂ, ℂ) v v))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    (∀ v : Place ℂ F, ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)) ∨ Set.Finite {v : Place ℂ F | ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)} := by
  classical
  set Bad : Set (Place ℂ F) := {v : Place ℂ F | ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)} with hBad
  have hmemBad : ∀ v, v ∈ Bad ↔ ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U) := fun v => by rw [hBad]; rfl

  have hBadc : IsClosed Bad := by
    have hGood : IsOpen {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} := (hw U hU 0).1
    have : Bad = {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U}ᶜ := by
      ext v; rw [hmemBad]; rfl
    rw [this]; exact hGood.isClosed_compl

  have L : ∀ v₀ ∈ Bad, (∃ D : Set (Place ℂ F), IsOpen D ∧ v₀ ∈ D ∧ D ⊆ Bad) ∨ (∀ᶠ v in 𝓝[≠] v₀, v ∉ Bad) := by
    intro v₀ hv₀

    obtain ⟨_, ⟨U'', hU''mem, rfl⟩, hQU'', -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((w v₀).1.base (IsLocalRing.closedPoint ℂ))) isOpen_univ
    have hU''aff : IsAffineOpen U'' := hU''mem
    replace hQU'' : (w v₀).1.base (IsLocalRing.closedPoint ℂ) ∈ U'' := hQU''
    have hv₀U'' : ⊤ ≤ (w v₀).1 ⁻¹ᵁ U'' := (top_le_iff _ _).2 hQU''
    set S : Set (Place ℂ F) := {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U''} with hSdef
    have hmemS : ∀ v, v ∈ S ↔ ⊤ ≤ (w v).1 ⁻¹ᵁ U'' := fun v => by rw [hSdef]; rfl
    have hSo : IsOpen S := by rw [hSdef]; exact (hw U'' hU''aff 0).1
    obtain ⟨D, hDo, hDconn, hv₀D, hDS⟩ := exists_chart_disc v₀ S hSo ((hmemS v₀).2 hv₀U'')
    by_cases hDB : D ⊆ Bad
    · exact Or.inl ⟨D, hDo, hv₀D, hDB⟩
    · right
      obtain ⟨v₁, hv₁D, hv₁B⟩ := Set.not_subset.1 hDB
      have hv₁U : ⊤ ≤ (w v₁).1 ⁻¹ᵁ U := by rw [hmemBad, not_not] at hv₁B; exact hv₁B
      have hv₁U'' : ⊤ ≤ (w v₁).1 ⁻¹ᵁ U'' := (hmemS v₁).1 (hDS hv₁D)
      have hQ₁U : (w v₁).1.base (IsLocalRing.closedPoint ℂ) ∈ U := (top_le_iff _ _).1 hv₁U
      have hQ₁U'' : (w v₁).1.base (IsLocalRing.closedPoint ℂ) ∈ U'' := (top_le_iff _ _).1 hv₁U''
      obtain ⟨b, hbU, hQ₁b⟩ := IsAffineOpen.exists_basicOpen_le hU''aff
        (⟨(w v₁).1.base (IsLocalRing.closedPoint ℂ), hQ₁U⟩ : U) hQ₁U''
      obtain ⟨-, G, hGval, hGdiff⟩ := hw U'' hU''aff b
      have hGdiff' : ∀ v ∈ S, DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
          (extChartAt 𝓘(ℂ, ℂ) v v) := fun v hv => hGdiff v ((hmemS v).1 hv)
      have hGan : ∀ x ∈ D, AnalyticAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
          (extChartAt 𝓘(ℂ, ℂ) x x) := fun x hx => analyticAt_extChartAt hSo G hGdiff' (hDS hx)
      have hGne : ∀ (v : Place ℂ F) (hv : ⊤ ≤ (w v).1 ⁻¹ᵁ U''),
          (G v ≠ 0 ↔ (w v).1.base (IsLocalRing.closedPoint ℂ) ∈ Y.basicOpen b) := by
        intro v hv; rw [hGval v hv]; exact val_ne_zero_iff (w v).1 U'' hv b
      rcases Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
          hDo hDconn G hGan with hzero | hiso
      · exact absurd (hzero v₁ hv₁D) ((hGne v₁ hv₁U'').2 hQ₁b)
      · have h1 := hiso v₀ hv₀D
        have h2 : ∀ᶠ v in 𝓝[≠] v₀, v ∈ S := mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds ((hmemS v₀).2 hv₀U''))
        filter_upwards [h1, h2] with v hv hvS
        have hmem : (w v).1.base (IsLocalRing.closedPoint ℂ) ∈ Y.basicOpen b := (hGne v ((hmemS v).1 hvS)).1 hv
        rw [hmemBad, not_not]
        exact (top_le_iff _ _).2 (hbU hmem)

  have hIntClosed : IsClosed (interior Bad) := by
    rw [← closure_subset_iff_isClosed]
    intro v₀ hv₀
    have hv₀B : v₀ ∈ Bad := hBadc.closure_subset (closure_mono interior_subset hv₀)
    rcases L v₀ hv₀B with ⟨D, hDo, hvD, hDB⟩ | hpunct
    · exact mem_interior.2 ⟨D, hDB, hDo, hvD⟩
    · by_contra hnot
      rw [mem_closure_iff_nhdsWithin_neBot] at hv₀
      have hle : 𝓝[interior Bad] v₀ ≤ 𝓝[≠] v₀ :=
        nhdsWithin_mono _ (fun v hv => fun heq => hnot (by rw [Set.mem_singleton_iff] at heq; rw [← heq]; exact hv))
      have hev : ∀ᶠ v in 𝓝[interior Bad] v₀, v ∉ Bad := hpunct.filter_mono hle
      have hev2 : ∀ᶠ v in 𝓝[interior Bad] v₀, v ∈ interior Bad := self_mem_nhdsWithin
      obtain ⟨v, hv1, hv2⟩ := (hev.and hev2).exists
      exact hv1 (interior_subset hv2)
  have hIntClopen : IsClopen (interior Bad) := ⟨hIntClosed, isOpen_interior⟩
  rcases isClopen_iff.1 hIntClopen with hempty | huniv
  ·
    right
    have hiso : ∀ v₀ ∈ Bad, ∀ᶠ v in 𝓝[≠] v₀, v ∉ Bad := by
      intro v₀ hv₀
      rcases L v₀ hv₀ with ⟨D, hDo, hvD, hDB⟩ | h
      · have : v₀ ∈ interior Bad := mem_interior.2 ⟨D, hDB, hDo, hvD⟩
        rw [hempty] at this
        exact this.elim
      · exact h
    have hO : ∀ v₀ ∈ Bad, ∃ O : Set (Place ℂ F), IsOpen O ∧ v₀ ∈ O ∧ O ∩ Bad ⊆ {v₀} := by
      intro v₀ hv₀
      obtain ⟨t, ht, hto, hv₀t⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (hiso v₀ hv₀))
      refine ⟨t, hto, hv₀t, fun v hv => ?_⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      exact ht v hv.1 hne hv.2
    choose O hO1 hO2 hO3 using hO
    have hBcpt : IsCompact Bad := hBadc.isCompact
    obtain ⟨s, hs⟩ := hBcpt.elim_finite_subcover (fun v : ↥Bad => O v.1 v.2) (fun v => hO1 v.1 v.2)
      (fun v hv => Set.mem_iUnion.2 ⟨⟨v, hv⟩, hO2 v hv⟩)
    have hfin : Set.Finite ((fun v : ↥Bad => (v : Place ℂ F)) '' (s : Set ↥Bad)) := s.finite_toSet.image _
    refine (hfin.subset ?_)
    intro v hv
    have hvB : v ∈ Bad := by rw [hmemBad]; exact hv
    obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.1 (hs hvB)
    have : v ∈ ({(i : Place ℂ F)} : Set (Place ℂ F)) := hO3 i.1 i.2 ⟨hvi, hvB⟩
    rw [Set.mem_singleton_iff] at this
    exact ⟨i, hi, this.symm⟩
  · left
    intro v
    have : v ∈ interior Bad := by rw [huniv]; trivial
    exact (hmemBad v).1 (interior_subset this)

end S_AlgebraicCurve_Place_forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
end P2MW
export P2MW.S_AlgebraicCurve_Place_forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated (solution)
