-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:56.185275+00:00
-- url     : https://prove2.me/theorems/b8c5cf5a-34f7-4084-91eb-a7d170ff8355
-- title:
--   Local Resolution Data
-- statement:
--   Definitions and structural lemmas for Local Resolution Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_lastStructMap_eq_projectionToBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}}
def SequenceOfBlowups.schemeAtIsoOfEq (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) : s.schemeAt i ≅ s.schemeAt j :=
  eqToIso (congrArg s.schemeAt h)
end
structure BlowupSequencePullbackComparison {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) where
  reindex : ℕ → ℕ
  iso : ∀ i : ℕ, i ≤ s'.length →
    (s'.schemeAt i ≅ (pullback φ (s.projectionToBase (reindex i)) : Scheme.{u}))
  reindex_length : reindex s'.length = s.length
  retention : ∀ i : ℕ, i < s.length →
    ((∃ j : ℕ, ∃ _ : j < s'.length, reindex j = i) ↔
      ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support)
  iso_hom_fst : ∀ (i : ℕ) (h : i ≤ s'.length),
    (iso i h).hom ≫ pullback.fst φ (s.projectionToBase (reindex i)) = s'.projectionToBase i
  center_eq : ∀ (i : ℕ) (h : i < s'.length),
    s'.center i =
      (s.center (reindex i)).comap
        ((iso i h.le).hom ≫ pullback.snd φ (s.projectionToBase (reindex i)))
theorem nonempty_pullbackComparison_of_isPullback {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) (h : IsPullbackBlowupSequence φ s' s) : Nonempty (BlowupSequencePullbackComparison φ s' s) := by
  unfold IsPullbackBlowupSequence at h
  obtain ⟨r, e, hlt, hmono, hlen, hret, hfst, hblow, hcen⟩ := h
  have hret' : ∀ i : ℕ, i < s.length →
      ((∃ j : ℕ, ∃ _ : j < s'.length, r j = i) ↔
        ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) := by
    intro i hi
    refine ⟨fun hj => (hret i hi).2 ?_, fun hx => ?_⟩
    · obtain ⟨j, hj1, hj2⟩ := hj
      exact ⟨j, hj1, hj2⟩
    · obtain ⟨j, hj1, hj2⟩ := (hret i hi).1 hx
      exact ⟨j, hj1, hj2⟩
  exact ⟨⟨r, e, hlen, hret', hfst, hcen⟩⟩
structure LocalResolutionData (k : Type u) [instFieldk : Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (s : SequenceOfBlowups X) where
  cover : Scheme.OpenCover.{u, u} X
  seq : ∀ i : cover.I₀, SequenceOfBlowups (cover.X i)
  isPullback : ∀ i : cover.I₀, IsPullbackBlowupSequence (cover.f i) (seq i) s
  finiteType : ∀ i : cover.I₀, LocallyOfFiniteType (cover.f i ≫ f)
  isResolution : ∀ i : cover.I₀,
    @IsStrongResolution k instFieldk (cover.X i) (cover.f i ≫ f) (finiteType i) (seq i)
attribute [instance] LocalResolutionData.finiteType
namespace LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
def comparison (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    BlowupSequencePullbackComparison (d.cover.f i) (d.seq i) s :=
  (nonempty_pullbackComparison_of_isPullback (d.cover.f i) (d.seq i) s (d.isPullback i)).some
def reindex (d : LocalResolutionData k f s) (i : d.cover.I₀) : ℕ → ℕ := (d.comparison i).reindex
def schemeAtIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j ≤ (d.seq i).length) :
    ((d.seq i).schemeAt j ≅ (pullback (d.cover.f i) (s.projectionToBase (d.reindex i j)) : Scheme.{u})) :=
  (d.comparison i).iso j hj
theorem reindex_length (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.reindex i (d.seq i).length = s.length :=
  (d.comparison i).reindex_length
theorem pullback_projectionToBase_eq_pullback_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) := by
  have h1 : (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u}) :=
    congrArg (fun n : ℕ => (pullback (d.cover.f i) (s.projectionToBase n) : Scheme.{u}))
      (d.reindex_length i)
  have h2 : (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) :=
    congrArg (fun g : s.lastObj ⟶ X => (pullback (d.cover.f i) g : Scheme.{u}))
      s.lastStructMap_eq_projectionToBase.symm
  exact h1.trans h2
def lastObjIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((d.seq i).lastObj ≅ (pullback (d.cover.f i) s.lastStructMap : Scheme.{u})) :=
  (d.schemeAtIsoPullback i (d.seq i).length le_rfl).trans (eqToIso (d.pullback_projectionToBase_eq_pullback_lastStructMap i))
theorem base_comp_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (t : ↥A) :
    (a ≫ b).base t = b.base (a.base t) := by
  simp
def chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) : (d.seq i).lastObj ⟶ s.lastObj :=
  (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap
theorem chartToLastObj_eq (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.chartToLastObj i = (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap :=
  rfl
theorem isOpenImmersion_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  rw [d.chartToLastObj_eq i]
  infer_instance
instance instIsOpenImmersionChartEmbedding (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) :=
  d.isOpenImmersion_chartToLastObj i
theorem exists_chartToLastObj_eq (d : LocalResolutionData k f s) (x : ↥(s.lastObj)) :
    ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i).base y = x := by
  obtain ⟨w, hw⟩ := d.cover.covers (s.lastStructMap.base x)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
  refine ⟨d.cover.idx (s.lastStructMap.base x), (d.lastObjIsoPullback _).inv.base p, ?_⟩
  have h2 : (d.lastObjIsoPullback (d.cover.idx (s.lastStructMap.base x))).inv ≫
      d.chartToLastObj (d.cover.idx (s.lastStructMap.base x))
      = pullback.snd (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap := by
    rw [d.chartToLastObj_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h3 := congrArg
    (fun m : (pullback (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap : Scheme.{u}) ⟶ s.lastObj
      => m.base p) h2
  simp only [base_comp_apply] at h3
  exact h3.trans hp2
theorem exists_chartToLastObj_apply_eq (d : LocalResolutionData k f s) :
    ∀ x : ↥(s.lastObj), ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i) y = x :=
  fun x => d.exists_chartToLastObj_eq x
def lastObjCover (d : LocalResolutionData k f s) : Scheme.OpenCover.{u, u} s.lastObj :=
  Scheme.Cover.mkOfCovers d.cover.I₀ (fun i => (d.seq i).lastObj)
    (fun i => d.chartToLastObj i) d.exists_chartToLastObj_apply_eq
    (fun i => d.isOpenImmersion_chartToLastObj i)
end LocalResolutionData
end FunctorialResolution.EmbeddedResolution
end


