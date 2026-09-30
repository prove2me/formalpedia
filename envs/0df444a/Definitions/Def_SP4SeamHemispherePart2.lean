-- Prove2me | Definitions.Def_SP4SeamHemispherePart2
-- name    : SP4SeamHemispherePart2
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T06:58:50.69638+00:00
-- url     : https://prove2.me/theorems/018645a5-a6d2-457c-85a9-de8a8391673e
-- title:
--   Open seam, interior homeomorphisms, and regional charts
-- statement:
--   For the same quotient $Q_\varphi$, the seam map identifies $S^m\times(-1,1)$ homeomorphically with the open seam $U_\varphi$. The two open disk-interior images $V_L,V_R$ are homeomorphic to the Euclidean open unit ball, and $U_\varphi,V_L,V_R$ cover the quotient. The interiors use their Euclidean coordinates. The seam uses standard sphere charts times the interval coordinate, followed by the linear identification $\mathbb R^m\times\mathbb R\to\mathbb R^{m+1}$ sending $(a,t)$ to $(t,a)$. For an open region $V$, its regional chart at $x\in V$ is obtained by composing its chart with the partial inverse of the inclusion $V\hookrightarrow Q_\varphi$. This part supplies the homeomorphisms, regional charted-space instances, regional partial homeomorphisms, and chart-selection function, with the proofs needed to construct them. These are specific charts on the glued quotient, not an atlas transported from a global homeomorphism to the standard sphere.
-- source:
--   Ryan Shin, Hemisphere.lean, unpublished Lean source (2026), selected constructor/instance support in lines 1141–1855; supported-environment transcription SHA-256 6a3aff0ac5800716d2e07d947579fa7972003cef657f6c6d1d7846ce4bf29215. Extracted by Lean compiler declaration/reference oracles, with namespace-only adaptations; no tracked source commit is claimed.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts
import Definitions.Def_SP4SeamPullbackGroupoid
import Definitions.Def_SP4SeamDisk
import Definitions.Def_SP4SeamHemispherePart1

set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph
open SP4Seam.Homeomorph

open Set Metric

open scoped ContDiff Manifold

section Hemisphere

variable {m : ℕ}

lemma isOpen_openSeam
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    IsOpen (openSeam φ) := by
  have key : IsOpen (Quot.mk (GlueRel φ) ⁻¹' openSeam φ) := by
    rw [isOpen_sum_iff]
    constructor
    · have hset : Sum.inl ⁻¹' (Quot.mk (GlueRel φ) ⁻¹' openSeam φ) =
          { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | 1 / 2 < ‖w.val‖ } := by
        ext w; exact mem_openSeam_inl φ w
      rw [hset]
      exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
    · have hset : Sum.inr ⁻¹' (Quot.mk (GlueRel φ) ⁻¹' openSeam φ) =
          { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | 1 / 2 < ‖w.val‖ } := by
        ext w; exact mem_openSeam_inr φ w
      rw [hset]
      exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  exact isOpen_coinduced.mpr key

instance twistedSphereT2Space
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    T2Space (TwistedSphere φ) :=
  (twistedSphereHomeoSphere φ).symm.t2Space

instance seamDomainCompactSpace : CompactSpace (Set.Icc (-1 : ℝ) 1) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

theorem isClosedEmbedding_seamMap
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Topology.IsClosedEmbedding (seamMap φ) :=
  (continuous_seamMap φ).isClosedEmbedding (injective_seamMap φ)

lemma range_seamMap_restrict
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Set.range (seamMap φ ∘ (Subtype.val :
      { p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1 //
        -1 < p.2.val ∧ p.2.val < 1 } → _)) = openSeam φ := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

noncomputable def seamHomeo
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    { p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1 //
      -1 < p.2.val ∧ p.2.val < 1 } ≃ₜ openSeam φ :=
  (((isClosedEmbedding_seamMap φ).toIsEmbedding.comp
    Topology.IsEmbedding.subtypeVal).toHomeomorph).trans
    (Homeomorph.setCongr (range_seamMap_restrict φ))

def interiorFst
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Set (TwistedSphere φ) :=
  (fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
    Quot.mk (GlueRel φ) (Sum.inl w)) '' { w | ‖w.val‖ < 1 }

def interiorSnd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Set (TwistedSphere φ) :=
  (fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
    Quot.mk (GlueRel φ) (Sum.inr w)) '' { w | ‖w.val‖ < 1 }

lemma mem_interiorFst_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ interiorFst φ ↔
      ‖w.val‖ < 1 := by
  constructor
  · rintro ⟨w', hw', heq⟩
    have : w' = w :=
      upperHemisphereHomeoDisk.symm.injective
        (Subtype.ext (congrArg (twistedGlueToSphere φ) heq))
    rwa [← this]
  · intro hw; exact ⟨w, hw, rfl⟩

lemma mem_interiorFst_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ interiorFst φ ↔ False := by
  simp only [iff_false]
  rintro ⟨w', hw', heq⟩
  have h1 := (norms_eq_one_of_glue_eq φ w' w heq).1
  have hlt : ‖w'.val‖ < 1 := hw'
  rw [h1] at hlt
  exact lt_irrefl 1 hlt

lemma mem_interiorSnd_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ interiorSnd φ ↔
      ‖w.val‖ < 1 := by
  constructor
  · rintro ⟨w', hw', heq⟩
    have hval : (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w')).val =
        (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w)).val :=
      congrArg (twistedGlueToSphere φ) heq
    have h2 : alexanderExt φ.symm w' = alexanderExt φ.symm w :=
      lowerHemisphereHomeoDiskRefl.symm.injective (Subtype.ext hval)
    have e1 : alexanderExt φ (alexanderExt φ.symm w') = w' := by
      have hx := alexanderExt_symm_alexanderExt φ.symm w'
      rwa [Homeomorph.symm_symm] at hx
    have e2 : alexanderExt φ (alexanderExt φ.symm w) = w := by
      have hx := alexanderExt_symm_alexanderExt φ.symm w
      rwa [Homeomorph.symm_symm] at hx
    have : w' = w := by rw [← e1, ← e2, h2]
    rwa [← this]
  · intro hw; exact ⟨w, hw, rfl⟩

lemma mem_interiorSnd_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ interiorSnd φ ↔ False := by
  simp only [iff_false]
  rintro ⟨w', hw', heq⟩
  have h1 := (norms_eq_one_of_glue_eq φ w w' heq.symm).2
  have hlt : ‖w'.val‖ < 1 := hw'
  rw [h1] at hlt
  exact lt_irrefl 1 hlt

lemma isOpen_interiorFst
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    IsOpen (interiorFst φ) := by
  have key : IsOpen (Quot.mk (GlueRel φ) ⁻¹' interiorFst φ) := by
    rw [isOpen_sum_iff]
    constructor
    · have hset : Sum.inl ⁻¹' (Quot.mk (GlueRel φ) ⁻¹' interiorFst φ) =
          { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | ‖w.val‖ < 1 } := by
        ext w; exact mem_interiorFst_inl φ w
      rw [hset]
      exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
    · have hset : Sum.inr ⁻¹' (Quot.mk (GlueRel φ) ⁻¹' interiorFst φ) = ∅ := by
        ext w; exact mem_interiorFst_inr φ w
      rw [hset]; exact isOpen_empty
  exact isOpen_coinduced.mpr key

lemma isOpen_interiorSnd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    IsOpen (interiorSnd φ) := by
  have key : IsOpen (Quot.mk (GlueRel φ) ⁻¹' interiorSnd φ) := by
    rw [isOpen_sum_iff]
    constructor
    · have hset : Sum.inl ⁻¹' (Quot.mk (GlueRel φ) ⁻¹' interiorSnd φ) = ∅ := by
        ext w; exact mem_interiorSnd_inl φ w
      rw [hset]; exact isOpen_empty
    · have hset : Sum.inr ⁻¹' (Quot.mk (GlueRel φ) ⁻¹' interiorSnd φ) =
          { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | ‖w.val‖ < 1 } := by
        ext w; exact mem_interiorSnd_inr φ w
      rw [hset]
      exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  exact isOpen_coinduced.mpr key

lemma openSeam_union_interiors
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    openSeam φ ∪ interiorFst φ ∪ interiorSnd φ = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, Set.mem_union]
  induction x using Quot.ind with
  | _ a =>
  match a with
  | Sum.inl w =>
    by_cases hw : 1 / 2 < ‖w.val‖
    · exact Or.inl (Or.inl ((mem_openSeam_inl φ w).mpr hw))
    · refine Or.inl (Or.inr ((mem_interiorFst_inl φ w).mpr ?_))
      push_neg at hw; linarith
  | Sum.inr w =>
    by_cases hw : 1 / 2 < ‖w.val‖
    · exact Or.inl (Or.inl ((mem_openSeam_inr φ w).mpr hw))
    · refine Or.inr ((mem_interiorSnd_inr φ w).mpr ?_)
      push_neg at hw; linarith

lemma isOpen_image_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {U : Set (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)} (hU : IsOpen U)
    (hUball : ∀ w ∈ U, ‖w.val‖ < 1) :
    IsOpen ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ)) '' U) := by
  have key : IsOpen (Quot.mk (GlueRel φ) ⁻¹'
      ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
        (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ)) '' U)) := by
    rw [isOpen_sum_iff]
    constructor
    · have hset : Sum.inl ⁻¹' (Quot.mk (GlueRel φ) ⁻¹'
          ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
            (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ)) '' U)) = U := by
        ext w
        constructor
        · rintro ⟨w', hw', heq⟩
          have hww : w' = w :=
            upperHemisphereHomeoDisk.symm.injective
              (Subtype.ext (congrArg (twistedGlueToSphere φ) heq))
          rwa [← hww]
        · intro hw; exact ⟨w, hw, rfl⟩
      rw [hset]; exact hU
    · have hset : Sum.inr ⁻¹' (Quot.mk (GlueRel φ) ⁻¹'
          ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
            (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ)) '' U)) = ∅ := by
        ext w
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨w', hw', heq⟩
        have h1 := (norms_eq_one_of_glue_eq φ w' w heq).1
        have := hUball w' hw'
        rw [h1] at this
        exact lt_irrefl 1 this
      rw [hset]; exact isOpen_empty
  exact isOpen_coinduced.mpr key

noncomputable def interiorFstEquiv
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 // ‖w.val‖ < 1 } ≃
      interiorFst φ where
  toFun w := ⟨Quot.mk (GlueRel φ) (Sum.inl w.val),
    (mem_interiorFst_inl φ w.val).mpr w.2⟩
  invFun x := ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  left_inv w := by
    apply Subtype.ext
    have hx : (Quot.mk (GlueRel φ) (Sum.inl w.val) : TwistedSphere φ) ∈ interiorFst φ :=
      (mem_interiorFst_inl φ w.val).mpr w.2
    exact upperHemisphereHomeoDisk.symm.injective
      (Subtype.ext (congrArg (twistedGlueToSphere φ) (Classical.choose_spec hx).2))
  right_inv x := Subtype.ext (Classical.choose_spec x.2).2

noncomputable def interiorFstHomeo
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 // ‖w.val‖ < 1 } ≃ₜ
      interiorFst φ :=
  (interiorFstEquiv φ).toHomeomorphOfContinuousOpen
    (Continuous.subtype_mk
      (continuous_quot_mk.comp (continuous_inl.comp continuous_subtype_val)) _)
    (by
      intro U hU
      have himg : (Subtype.val : interiorFst φ → TwistedSphere φ) ''
          ((interiorFstEquiv φ) '' U) =
          (fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
            (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ)) ''
            (Subtype.val '' U) := by
        ext x
        constructor
        · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨w.val, ⟨w, hw, rfl⟩, rfl⟩
        · rintro ⟨w, ⟨w', hw', rfl⟩, rfl⟩
          exact ⟨_, ⟨w', hw', rfl⟩, rfl⟩
      rw [(isOpen_interiorFst φ).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
        himg]
      exact isOpen_image_inl φ
        ((isOpen_lt (continuous_norm.comp continuous_subtype_val)
          continuous_const).isOpenMap_subtype_val U hU)
        (by rintro w ⟨w', hw', rfl⟩; exact w'.2))

lemma inr_quot_injective
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {w w' : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) =
      Quot.mk _ (Sum.inr w')) : w = w' := by
  have hval : (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w)).val =
      (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w')).val :=
    congrArg (twistedGlueToSphere φ) h
  have h2 : alexanderExt φ.symm w = alexanderExt φ.symm w' :=
    lowerHemisphereHomeoDiskRefl.symm.injective (Subtype.ext hval)
  have e1 : alexanderExt φ (alexanderExt φ.symm w) = w := by
    have hx := alexanderExt_symm_alexanderExt φ.symm w
    rwa [Homeomorph.symm_symm] at hx
  have e2 : alexanderExt φ (alexanderExt φ.symm w') = w' := by
    have hx := alexanderExt_symm_alexanderExt φ.symm w'
    rwa [Homeomorph.symm_symm] at hx
  rw [← e1, ← e2, h2]

lemma isOpen_image_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {U : Set (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)} (hU : IsOpen U)
    (hUball : ∀ w ∈ U, ‖w.val‖ < 1) :
    IsOpen ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ)) '' U) := by
  have key : IsOpen (Quot.mk (GlueRel φ) ⁻¹'
      ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
        (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ)) '' U)) := by
    rw [isOpen_sum_iff]
    constructor
    · have hset : Sum.inl ⁻¹' (Quot.mk (GlueRel φ) ⁻¹'
          ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
            (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ)) '' U)) = ∅ := by
        ext w
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨w', hw', heq⟩
        have h1 := (norms_eq_one_of_glue_eq φ w w' heq.symm).2
        have hlt : ‖w'.val‖ < 1 := hUball w' hw'
        rw [h1] at hlt
        exact lt_irrefl 1 hlt
      rw [hset]; exact isOpen_empty
    · have hset : Sum.inr ⁻¹' (Quot.mk (GlueRel φ) ⁻¹'
          ((fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
            (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ)) '' U)) = U := by
        ext w
        constructor
        · rintro ⟨w', hw', heq⟩
          rwa [inr_quot_injective φ heq] at hw'
        · intro hw; exact ⟨w, hw, rfl⟩
      rw [hset]; exact hU
  exact isOpen_coinduced.mpr key

noncomputable def interiorSndEquiv
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 // ‖w.val‖ < 1 } ≃
      interiorSnd φ where
  toFun w := ⟨Quot.mk (GlueRel φ) (Sum.inr w.val),
    (mem_interiorSnd_inr φ w.val).mpr w.2⟩
  invFun x := ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  left_inv w := by
    apply Subtype.ext
    have hx : (Quot.mk (GlueRel φ) (Sum.inr w.val) : TwistedSphere φ) ∈ interiorSnd φ :=
      (mem_interiorSnd_inr φ w.val).mpr w.2
    exact inr_quot_injective φ (Classical.choose_spec hx).2
  right_inv x := Subtype.ext (Classical.choose_spec x.2).2

noncomputable def interiorSndHomeo
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 // ‖w.val‖ < 1 } ≃ₜ
      interiorSnd φ :=
  (interiorSndEquiv φ).toHomeomorphOfContinuousOpen
    (Continuous.subtype_mk
      (continuous_quot_mk.comp (continuous_inr.comp continuous_subtype_val)) _)
    (by
      intro U hU
      have himg : (Subtype.val : interiorSnd φ → TwistedSphere φ) ''
          ((interiorSndEquiv φ) '' U) =
          (fun w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
            (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ)) ''
            (Subtype.val '' U) := by
        ext x
        constructor
        · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨w.val, ⟨w, hw, rfl⟩, rfl⟩
        · rintro ⟨w, ⟨w', hw', rfl⟩, rfl⟩
          exact ⟨_, ⟨w', hw', rfl⟩, rfl⟩
      rw [(isOpen_interiorSnd φ).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
        himg]
      exact isOpen_image_inr φ
        ((isOpen_lt (continuous_norm.comp continuous_subtype_val)
          continuous_const).isOpenMap_subtype_val U hU)
        (by rintro w ⟨w', hw', rfl⟩; exact w'.2))

def seamModelLinearEquiv (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun p := WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i))
  invFun v := (WithLp.toLp 2 (Fin.tail (fun i => v i)), v 0)
  map_add' a b := by
    apply WithLp.ofLp_injective
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ i => simp
  map_smul' c a := by
    apply WithLp.ofLp_injective
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ i => simp
  left_inv p := by
    apply Prod.ext
    · apply WithLp.ofLp_injective
      funext i
      simp [Fin.tail]
    · simp
  right_inv v := by
    apply WithLp.ofLp_injective
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ i => simp [Fin.tail]

noncomputable def seamModelEquiv (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (seamModelLinearEquiv m).toContinuousLinearEquiv

def seamDomainHomeo :
    { p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1 //
      -1 < p.2.val ∧ p.2.val < 1 } ≃ₜ
      (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Ioo (-1 : ℝ) 1) where
  toFun p := (p.val.1, ⟨p.val.2.val, p.2⟩)
  invFun q := ⟨(q.1, ⟨q.2.val, ⟨le_of_lt q.2.2.1, le_of_lt q.2.2.2⟩⟩), q.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext rfl
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Prod.ext rfl
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_snd

noncomputable def seamHomeoIoo
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Ioo (-1 : ℝ) 1) ≃ₜ
      openSeam φ :=
  seamDomainHomeo.symm.trans (seamHomeo φ)

instance iooNonempty : Nonempty (Set.Ioo (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩

noncomputable instance iooChartedSpace :
    ChartedSpace ℝ (Set.Ioo (-1 : ℝ) 1) :=
  (isOpen_Ioo.isOpenEmbedding_subtypeVal).singletonChartedSpace

noncomputable instance modelProdChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1)))
      (ModelProd (EuclideanSpace ℝ (Fin m)) ℝ) :=
  ((seamModelEquiv m).toHomeomorph).sp4MissionPullbackChartedSpace

noncomputable instance seamProdChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Ioo (-1 : ℝ) 1) :=
  ChartedSpace.comp (EuclideanSpace ℝ (Fin (m + 1)))
    (ModelProd (EuclideanSpace ℝ (Fin m)) ℝ) _

noncomputable instance openSeamChartedSpace
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (openSeam φ) :=
  (seamHomeoIoo φ).symm.sp4MissionPullbackChartedSpace

def ballSubtypeHomeo :
    { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 // ‖w.val‖ < 1 } ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 where
  toFun w := ⟨w.val.val, by rw [mem_ball_zero_iff]; exact w.2⟩
  invFun x := ⟨⟨x.val, by
      rw [mem_closedBall_zero_iff]
      exact le_of_lt (mem_ball_zero_iff.mp x.2)⟩, mem_ball_zero_iff.mp x.2⟩
  left_inv w := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

instance ballNonempty :
    Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
  ⟨⟨0, by simp⟩⟩

noncomputable instance ballChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
  (Metric.isOpen_ball.isOpenEmbedding_subtypeVal).singletonChartedSpace

noncomputable instance ballInteriorChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1)))
      { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 // ‖w.val‖ < 1 } :=
  ballSubtypeHomeo.sp4MissionPullbackChartedSpace

noncomputable instance interiorFstChartedSpace
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (interiorFst φ) :=
  (interiorFstHomeo φ).symm.sp4MissionPullbackChartedSpace

noncomputable instance interiorSndChartedSpace
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (interiorSnd φ) :=
  (interiorSndHomeo φ).symm.sp4MissionPullbackChartedSpace

noncomputable def regionChart
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {S : Set (TwistedSphere φ)} (hS : IsOpen S)
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) S] (x : S) :
    OpenPartialHomeomorph (TwistedSphere φ) (EuclideanSpace ℝ (Fin (m + 1))) :=
  letI : Nonempty S := ⟨x⟩
  (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Subtype.val : S → TwistedSphere φ)
    hS.isOpenEmbedding_subtypeVal).symm.trans
    (chartAt (EuclideanSpace ℝ (Fin (m + 1))) x)

lemma mem_regionChart_source
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    {S : Set (TwistedSphere φ)} (hS : IsOpen S)
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) S] (x : S) :
    (x : TwistedSphere φ) ∈ (regionChart hS x).source := by
  letI : Nonempty S := ⟨x⟩
  rw [regionChart, OpenPartialHomeomorph.trans_source]
  constructor
  · simp only [OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨x, rfl⟩
  · simp only [Set.mem_preimage]
    rw [show (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : S → TwistedSphere φ) hS.isOpenEmbedding_subtypeVal).symm
      (x : TwistedSphere φ) = x from
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _]
    exact mem_chart_source _ x

open scoped Classical in

noncomputable def twistedChartAt
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : TwistedSphere φ) :
    OpenPartialHomeomorph (TwistedSphere φ) (EuclideanSpace ℝ (Fin (m + 1))) :=
  if h : x ∈ openSeam φ then regionChart (isOpen_openSeam φ) ⟨x, h⟩
  else if h1 : x ∈ interiorFst φ then regionChart (isOpen_interiorFst φ) ⟨x, h1⟩
  else if h2 : x ∈ interiorSnd φ then regionChart (isOpen_interiorSnd φ) ⟨x, h2⟩
  else False.elim (by
    have hcov := openSeam_union_interiors φ
    have hx : x ∈ (Set.univ : Set (TwistedSphere φ)) := Set.mem_univ x
    rw [← hcov] at hx
    rcases hx with (hs | hf) | hsn
    · exact h hs
    · exact h1 hf
    · exact h2 hsn)

end Hemisphere

end SP4Seam


