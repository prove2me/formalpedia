-- Prove2me | Definitions.Def_SP4TransportBridge
-- name    : SP4TransportBridge
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:24:54.410709+00:00
-- url     : https://prove2.me/theorems/5ec3797c-4ce1-43fe-af06-16a1b993fad4
-- title:
--   Transport and structomorphism–diffeomorphism infrastructure
-- statement:
--   For topological spaces M,N, a topological chart model H, a structure groupoid G on H, a G-compatible H-charted structure on M and a homeomorphism e:N→M, the same homeomorphism defines a G-structomorphism when N is equipped with the pulled-back atlas. Separately, for every nontrivially normed field, model with corners I and differentiability order k, between Cᵏ manifolds over the same I, Cᵏ-groupoid structomorphisms and Cᵏ diffeomorphisms can be converted in both directions, preserving the underlying homeomorphism. Necessary closed proof support is included; no Poincaré or Freedman assertion is used.
-- source:
--   Unpublished local Lean source SPC4.lean, SHA-256 b17fdb932034e5211d0db8171c08e2b3a182016bceaecdd2deb49c39d6bfd5cc; supported copy and exact oracle provenance in the accompanying local package. Transported-chart construction and pullback compatibility also use the unpublished local PullbackGroupoid.lean source, SHA-256 f92aabb88c15cd62fd95afdeaa4c155b0daa62a8283b58a0848b576116fc8fa8.

-- Clean transport definitions and only their necessary proof support.
import Definitions.Def_SP4PullbackCharts

set_option autoImplicit false

namespace SP4Mission

open _root_.Homeomorph

open Set ChartedSpace

open scoped Manifold Topology

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N]

namespace Homeomorph

omit [ChartedSpace H M] in

private theorem symm_trans_toOpenPartialHomeomorph (e : N ≃ₜ M) :
    e.toOpenPartialHomeomorph.symm ≫ₕ e.toOpenPartialHomeomorph =
      OpenPartialHomeomorph.refl M := by
  rw [← symm_toOpenPartialHomeomorph, ← trans_toOpenPartialHomeomorph,
    symm_trans_self, refl_toOpenPartialHomeomorph]

omit [ChartedSpace H M] in

theorem pullback_symm_trans (e : N ≃ₜ M) (c c' : OpenPartialHomeomorph M H) :
    (e.transOpenPartialHomeomorph c).symm ≫ₕ e.transOpenPartialHomeomorph c' =
      c.symm ≫ₕ c' := by
  simp only [transOpenPartialHomeomorph_eq_trans]
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,
    symm_trans_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]

def _root_.Homeomorph.sp4MissionPullbackStructomorph (e : N ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI : ChartedSpace H N := e.sp4MissionPullbackChartedSpace
    Structomorph G N M := by
  let _ : ChartedSpace H N := e.sp4MissionPullbackChartedSpace
  refine { e with mem_groupoid := ?_ }
  rintro c c' ⟨c₀, hc₀, rfl⟩ hc'
  rw [← transOpenPartialHomeomorph_eq_trans, pullback_symm_trans]
  exact StructureGroupoid.compatible _ hc₀ hc'

end Homeomorph

end SP4Mission
namespace SP4Mission

open scoped Manifold ContDiff

noncomputable section

section Transport

variable {N : Type} [TopologicalSpace N]

end Transport

section Bridge

open Set ChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace H' X']
  {m : ℕ∞ω} [IsManifold I m X] [IsManifold I m X']

omit [IsManifold I m X] [IsManifold I m X'] in

theorem _root_.Structomorph.sp4MissionLiftPropOn (h : Structomorph (contDiffGroupoid m I) X X') :
    LiftPropOn (contDiffGroupoid m I).IsLocalStructomorphWithinAt
      h.toHomeomorph.toOpenPartialHomeomorph
      h.toHomeomorph.toOpenPartialHomeomorph.source := by
  intro x _
  refine ⟨h.continuous.continuousWithinAt, fun _ => ?_⟩
  refine ⟨(chartAt H' x).symm ≫ₕ h.toHomeomorph.toOpenPartialHomeomorph ≫ₕ
      chartAt H' (h.toHomeomorph x),
    h.mem_groupoid _ _ (chart_mem_atlas _ _) (chart_mem_atlas _ _), ?_, ?_⟩
  · exact fun y _ => rfl
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    refine ⟨?_, ?_, ?_⟩
    · exact (chartAt H' x).map_source (mem_chart_source H' x)
    · simp [Homeomorph.toOpenPartialHomeomorph_source,
        (chartAt H' x).left_inv (mem_chart_source H' x)]
    · simp [Homeomorph.toOpenPartialHomeomorph_apply,
        (chartAt H' x).left_inv (mem_chart_source H' x), mem_chart_source]

theorem _root_.Structomorph.sp4MissionContMDiff (h : Structomorph (contDiffGroupoid m I) X X') :
    ContMDiff I I m h.toHomeomorph := by
  have H2 := (isLocalStructomorphOn_contDiffGroupoid_iff
    h.toHomeomorph.toOpenPartialHomeomorph).mp h.sp4MissionLiftPropOn
  have hs : h.toHomeomorph.toOpenPartialHomeomorph.source = univ :=
    Homeomorph.toOpenPartialHomeomorph_source _
  rw [← contMDiffOn_univ, ← hs]
  exact H2.1

def _root_.Structomorph.sp4MissionToDiffeomorph (h : Structomorph (contDiffGroupoid m I) X X') :
    X ≃ₘ^m⟮I, I⟯ X' where
  toEquiv := h.toHomeomorph.toEquiv
  contMDiff_toFun := h.sp4MissionContMDiff
  contMDiff_invFun := h.symm.sp4MissionContMDiff

def _root_.Diffeomorph.sp4MissionToStructomorph (φ : X ≃ₘ^m⟮I, I⟯ X') :
    Structomorph (contDiffGroupoid m I) X X' where
  toHomeomorph := φ.toHomeomorph
  mem_groupoid := by
    intro c c' hc hc'
    set fm := φ.toHomeomorph.toOpenPartialHomeomorph with hfm
    have hsrc : fm.source = univ := Homeomorph.toOpenPartialHomeomorph_source _
    have htgt : fm.target = univ := Homeomorph.toOpenPartialHomeomorph_target _
    have hLP : LiftPropOn (contDiffGroupoid m I).IsLocalStructomorphWithinAt
        fm fm.source :=
      (isLocalStructomorphOn_contDiffGroupoid_iff fm).mpr
        ⟨hsrc ▸ φ.contMDiff.contMDiffOn, htgt ▸ φ.symm.contMDiff.contMDiffOn⟩
    apply StructureGroupoid.locality
    intro z hz
    have hz' : z ∈ c.target ∧ φ.toHomeomorph (c.symm z) ∈ c'.source := by
      simpa [hfm, OpenPartialHomeomorph.trans_source, hsrc] using hz
    set x := c.symm z with hxdef
    have hxc : x ∈ c.source := c.map_target hz'.1
    have hcx : c x = z := c.right_inv hz'.1
    have hLPx := hLP x (by simp [hsrc])
    rw [hsrc] at hLPx
    have h2 := ((StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid m I)).liftPropWithinAt_indep_chart
        ((contDiffGroupoid m I).subset_maximalAtlas hc) hxc
        ((contDiffGroupoid m I).subset_maximalAtlas hc') hz'.2).mp hLPx
    obtain ⟨e₀, he₀G, he₀eq, he₀z⟩ := h2.2 (by simp)
    rw [hcx] at he₀z
    set g := c.symm ≫ₕ fm ≫ₕ c' with hgdef
    have hgopen : IsOpen (e₀.source ∩ g.source) :=
      e₀.open_source.inter g.open_source
    refine ⟨e₀.source ∩ g.source, hgopen, ⟨he₀z, hz⟩, ?_⟩
    apply (contDiffGroupoid m I).mem_of_eqOnSource
      (closedUnderRestriction' he₀G hgopen)
    constructor
    · simp only [OpenPartialHomeomorph.restr_source, hgopen.interior_eq]
      mfld_set_tac
    · intro y hy
      have hy' : y ∈ univ ∩ e₀.source := by
        simp only [OpenPartialHomeomorph.restr_source, hgopen.interior_eq] at hy
        exact ⟨trivial, hy.2.1⟩
      exact he₀eq hy'

end Bridge

end

end SP4Mission


