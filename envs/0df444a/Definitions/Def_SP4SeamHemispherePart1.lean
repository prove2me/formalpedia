-- Prove2me | Definitions.Def_SP4SeamHemispherePart1
-- name    : SP4SeamHemispherePart1
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T06:57:47.189237+00:00
-- url     : https://prove2.me/theorems/8b26d35f-9a90-4af1-a9b0-1042ea7fd535
-- title:
--   Topological seam construction on the two-disk quotient
-- statement:
--   For $m\geq0$ and a homeomorphism $\varphi:S^m\to S^m$, use the quotient $Q_\varphi=(D_L^{m+1}\sqcup D_R^{m+1})/(u_L\sim\varphi(u)_R)$ with its quotient topology. The seam map on $S^m\times[-1,1]$ is
--   $$c_\varphi(u,t)=\begin{cases}[(1-t/2)u]_L,&t\geq0,\\[(1+t/2)\varphi(u)]_R,&t<0.\end{cases}$$
--   Its restriction to $S^m\times(-1,1)$ defines the open seam. This first part provides the piecewise radial maps and the proved continuity, injectivity, and membership facts needed for subsequent homeomorphism constructors. It reuses the existing quotient and disk-to-hemisphere data. The source's constructive topological homeomorphism to $S^{m+1}$ is retained as constructor support for the Hausdorff instance; it is not another public gluing theorem. No smoothness of this global homeomorphism is claimed.
-- source:
--   Ryan Shin, Hemisphere.lean, unpublished Lean source (2026), selected constructor/instance support in lines 190–1139; supported-environment transcription SHA-256 6a3aff0ac5800716d2e07d947579fa7972003cef657f6c6d1d7846ce4bf29215. Extracted by Lean compiler declaration/reference oracles, with namespace-only adaptations; no tracked source commit is claimed.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts
import Definitions.Def_SP4SeamPullbackGroupoid
import Definitions.Def_SP4SeamDisk

set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph
open SP4Seam.Homeomorph

open Set Metric

open scoped ContDiff Manifold

section Hemisphere

variable {m : ℕ}

lemma norm_hemisphereToDisk_eq_one_iff (x : upperHemisphere m) :
    ‖(hemisphereToDisk x).val‖ = 1 ↔ x.val.val 0 = 0 := by
  have hx : ‖x.val.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.val.2
  have hpos : 0 ≤ x.val.val 0 := x.2
  have htail := euclidean_norm_sq_tail (x.val.val)
  rw [hx] at htail
  show ‖(WithLp.toLp 2 (Fin.tail (fun i => x.val.val i)) :
    EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 ↔ _
  constructor
  · intro h
    rw [h] at htail
    nlinarith
  · intro h
    rw [h] at htail
    have h1 : ‖(WithLp.toLp 2 (Fin.tail (fun i => x.val.val i)) :
        EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 = 1 := by rw [htail]; ring
    nlinarith [norm_nonneg (WithLp.toLp 2 (Fin.tail (fun i => x.val.val i)) :
      EuclideanSpace ℝ (Fin (m + 1)))]

lemma hemisphere_identifications_agree
    (x : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)
    (hu : x ∈ upperHemisphere m) (hl : x ∈ lowerHemisphere m) :
    (hemisphereToDisk ⟨x, hu⟩ : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) =
      lowerHemisphereHomeoDiskRefl ⟨x, hl⟩ := by
  apply Subtype.ext
  show (WithLp.toLp 2 (Fin.tail (fun i => x.val i)) :
      EuclideanSpace ℝ (Fin (m + 1))) =
    (WithLp.toLp 2 (Fin.tail (fun i => reflectFirst x.val i)) :
      EuclideanSpace ℝ (Fin (m + 1)))
  apply WithLp.ofLp_injective
  funext j
  simp [reflectFirst, Fin.tail]

@[simp] lemma alexanderExt_norm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ‖(alexanderExt φ w).val‖ = ‖w.val‖ := by
  show ‖‖w.val‖ • (φ (unitOr diskNorth w.val)).val‖ = ‖w.val‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    mem_sphere_zero_iff_norm.mp (φ (unitOr diskNorth w.val)).2, mul_one]

lemma continuous_alexanderExt
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (alexanderExt φ) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro w
  by_cases h : w.val = 0
  · 
    have hnorm : Filter.Tendsto
        (fun w' : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 => ‖w'.val‖)
        (nhds w) (nhds 0) := by
      have hc : ContinuousAt
          (fun w' : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 => ‖w'.val‖) w :=
        (continuous_norm.comp continuous_subtype_val).continuousAt
      simpa [ContinuousAt, h] using hc
    have hsq : Filter.Tendsto
        (fun w' : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
          ‖w'.val‖ • (φ (unitOr diskNorth w'.val)).val) (nhds w) (nhds 0) :=
      squeeze_zero_norm (fun w' => le_of_eq (alexanderExt_norm φ w')) hnorm
    simpa [ContinuousAt, h] using hsq
  · 
    have hopen : { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } ∈ nhds w.val :=
      isOpen_ne.mem_nhds h
    have h1 : ContinuousAt (unitOr (n := m + 1) diskNorth) w.val :=
      (continuousOn_unitOr diskNorth).continuousAt hopen
    have h2 : ContinuousAt
        (fun w' : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
          unitOr diskNorth w'.val) w :=
      h1.comp continuous_subtype_val.continuousAt
    exact (continuous_norm.comp continuous_subtype_val).continuousAt.smul
      ((continuous_subtype_val.comp φ.continuous).continuousAt.comp h2)

lemma alexanderExt_symm_alexanderExt
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    alexanderExt φ.symm (alexanderExt φ w) = w := by
  apply Subtype.ext
  by_cases h : w.val = 0
  · show ‖(alexanderExt φ w).val‖ • _ = w.val
    rw [alexanderExt_norm, h, norm_zero, zero_smul]
  · have hpos : 0 < ‖w.val‖ := norm_pos_iff.mpr h
    show ‖(alexanderExt φ w).val‖ •
      (φ.symm (unitOr diskNorth (alexanderExt φ w).val)).val = w.val
    have hval : (alexanderExt φ w).val =
        ‖w.val‖ • (φ (unitOr diskNorth w.val)).val := rfl
    rw [alexanderExt_norm, hval, unitOr_smul diskNorth hpos,
      Homeomorph.symm_apply_apply, smul_unitOr diskNorth h]

lemma continuous_twistedGlueToSphere
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (twistedGlueToSphere φ) :=
  continuous_quot_lift _
    (Continuous.sumElim
      (continuous_subtype_val.comp upperHemisphereHomeoDisk.symm.continuous)
      ((continuous_subtype_val.comp lowerHemisphereHomeoDiskRefl.symm.continuous).comp
        (continuous_alexanderExt φ.symm)))

lemma surjective_twistedGlueToSphere
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Surjective (twistedGlueToSphere φ) := by
  intro x
  rcases le_total 0 (x.val 0) with h | h
  · refine ⟨Quot.mk _ (Sum.inl (hemisphereToDisk ⟨x, h⟩)), ?_⟩
    show (upperHemisphereHomeoDisk.symm (hemisphereToDisk ⟨x, h⟩)).val = x
    rw [show hemisphereToDisk (⟨x, h⟩ : upperHemisphere m) =
      upperHemisphereHomeoDisk ⟨x, h⟩ from rfl, Homeomorph.symm_apply_apply]
  · refine ⟨Quot.mk _ (Sum.inr
      (alexanderExt φ (lowerHemisphereHomeoDiskRefl ⟨x, h⟩))), ?_⟩
    show (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm
      (alexanderExt φ (lowerHemisphereHomeoDiskRefl ⟨x, h⟩)))).val = x
    rw [alexanderExt_symm_alexanderExt, Homeomorph.symm_apply_apply]

lemma twisted_glue_eq_of_inl_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w₁ w₂ : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (hab : (upperHemisphereHomeoDisk.symm w₁).val =
      (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w₂)).val) :
    (Quot.mk (GlueRel φ) (Sum.inl w₁) : TwistedSphere φ) =
      Quot.mk _ (Sum.inr w₂) := by
  set v := alexanderExt φ.symm w₂ with hv
  set p := upperHemisphereHomeoDisk.symm w₁ with hp
  set q := lowerHemisphereHomeoDiskRefl.symm v with hq
  have hw₁ : hemisphereToDisk p = w₁ := upperHemisphereHomeoDisk.apply_symm_apply w₁
  have hw₂ : lowerHemisphereHomeoDiskRefl q = v :=
    lowerHemisphereHomeoDiskRefl.apply_symm_apply v
  have hu : p.val ∈ upperHemisphere m := p.2
  have hl : p.val ∈ lowerHemisphere m := by rw [hab]; exact q.2
  have hzero : p.val.val 0 = 0 := by
    have h1 : (0 : ℝ) ≤ p.val.val 0 := hu
    have h2 : p.val.val 0 ≤ 0 := hl
    linarith
  have hnorm : ‖w₁.val‖ = 1 := by
    rw [← hw₁]
    exact (norm_hemisphereToDisk_eq_one_iff p).mpr hzero
  set u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    ⟨w₁.val, mem_sphere_zero_iff_norm.mpr hnorm⟩ with hu_def
  have hsu : sphereToDisk u = w₁ := rfl
  have hagree := hemisphere_identifications_agree p.val hu hl
  have hqeq : (⟨p.val, hl⟩ : lowerHemisphere m) = q := Subtype.ext hab
  rw [Subtype.coe_eta, hw₁, hqeq, hw₂] at hagree
  have hinv : alexanderExt φ v = w₂ := by
    rw [hv]
    have h := alexanderExt_symm_alexanderExt φ.symm w₂
    rwa [Homeomorph.symm_symm] at h
  have hw₂' : w₂ = sphereToDisk (φ u) := by
    rw [← hinv, ← hagree, ← hsu, alexanderExt_sphereToDisk]
  rw [← hsu, hw₂']
  exact Quot.sound (GlueRel.glue u)

lemma injective_twistedGlueToSphere
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Injective (twistedGlueToSphere φ) := by
  intro a b hab
  induction a using Quot.ind with
  | _ a =>
  induction b using Quot.ind with
  | _ b =>
  match a, b with
  | Sum.inl w₁, Sum.inl w₂ =>
    have h : upperHemisphereHomeoDisk.symm w₁ = upperHemisphereHomeoDisk.symm w₂ :=
      Subtype.ext hab
    rw [upperHemisphereHomeoDisk.symm.injective h]
  | Sum.inr w₁, Sum.inr w₂ =>
    have h : lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w₁) =
        lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w₂) := Subtype.ext hab
    have h2 : alexanderExt φ.symm w₁ = alexanderExt φ.symm w₂ :=
      lowerHemisphereHomeoDiskRefl.symm.injective h
    have e1 : alexanderExt φ (alexanderExt φ.symm w₁) = w₁ := by
      have h := alexanderExt_symm_alexanderExt φ.symm w₁
      rwa [Homeomorph.symm_symm] at h
    have e2 : alexanderExt φ (alexanderExt φ.symm w₂) = w₂ := by
      have h := alexanderExt_symm_alexanderExt φ.symm w₂
      rwa [Homeomorph.symm_symm] at h
    rw [← e1, ← e2, h2]
  | Sum.inl w₁, Sum.inr w₂ =>
    exact twisted_glue_eq_of_inl_inr φ w₁ w₂ hab
  | Sum.inr w₁, Sum.inl w₂ =>
    exact (twisted_glue_eq_of_inl_inr φ w₂ w₁ hab.symm).symm

noncomputable def twistedSphereHomeoSphere
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    TwistedSphere φ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (twistedGlueToSphere φ)
      ⟨injective_twistedGlueToSphere φ, surjective_twistedGlueToSphere φ⟩)
    (continuous_twistedGlueToSphere φ)

noncomputable def seamBallFst
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1) :
    closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨min 1 (1 - p.2.val / 2) • p.1.val, by
    have ht : p.2.val ≤ 1 := p.2.2.2
    have h0 : (0 : ℝ) ≤ min 1 (1 - p.2.val / 2) := le_min zero_le_one (by linarith)
    have h1 : min 1 (1 - p.2.val / 2) ≤ 1 := min_le_left _ _
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0,
      mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
    exact h1⟩

noncomputable def seamBallSnd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1) :
    closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨min 1 (1 + p.2.val / 2) • (φ p.1).val, by
    have ht : (-1 : ℝ) ≤ p.2.val := p.2.2.1
    have h0 : (0 : ℝ) ≤ min 1 (1 + p.2.val / 2) := le_min zero_le_one (by linarith)
    have h1 : min 1 (1 + p.2.val / 2) ≤ 1 := min_le_left _ _
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0,
      mem_sphere_zero_iff_norm.mp (φ p.1).2, mul_one]
    exact h1⟩

noncomputable def seamMap
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1) :
    TwistedSphere φ :=
  if (0 : ℝ) ≤ p.2.val then Quot.mk _ (Sum.inl (seamBallFst p))
  else Quot.mk _ (Sum.inr (seamBallSnd φ p))

lemma continuous_seamBallFst : Continuous (seamBallFst (m := m)) := by
  apply Continuous.subtype_mk
  exact (continuous_const.min (continuous_const.sub
    ((continuous_subtype_val.comp continuous_snd).div_const 2))).smul
    (continuous_subtype_val.comp continuous_fst)

lemma continuous_seamBallSnd
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (seamBallSnd φ) := by
  apply Continuous.subtype_mk
  exact (continuous_const.min ((continuous_subtype_val.comp continuous_snd).div_const 2
    |>.const_add 1)).smul
    (continuous_subtype_val.comp (φ.continuous.comp continuous_fst))

lemma seam_agree
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (h : p.2.val = 0) :
    (Quot.mk _ (Sum.inl (seamBallFst p)) : TwistedSphere φ) =
      Quot.mk _ (Sum.inr (seamBallSnd φ p)) := by
  have hfst : seamBallFst p = sphereToDisk p.1 := by
    apply Subtype.ext
    show min 1 (1 - p.2.val / 2) • p.1.val = p.1.val
    rw [h]
    norm_num
  have hsnd : seamBallSnd φ p = sphereToDisk (φ p.1) := by
    apply Subtype.ext
    show min 1 (1 + p.2.val / 2) • (φ p.1).val = (φ p.1).val
    rw [h]
    norm_num
  rw [hfst, hsnd]
  exact Quot.sound (GlueRel.glue p.1)

lemma continuous_seamMap
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (seamMap φ) :=
  Continuous.if_le
    (continuous_quot_mk.comp (continuous_inl.comp continuous_seamBallFst))
    (continuous_quot_mk.comp (continuous_inr.comp (continuous_seamBallSnd φ)))
    continuous_const (continuous_subtype_val.comp continuous_snd)
    (fun p hp => seam_agree φ p hp.symm)

lemma seamBallFst_norm
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (h : 0 ≤ p.2.val) : ‖(seamBallFst p).val‖ = 1 - p.2.val / 2 := by
  have ht : p.2.val ≤ 1 := p.2.2.2
  have hmin : min 1 (1 - p.2.val / 2) = 1 - p.2.val / 2 := min_eq_right (by linarith)
  show ‖min 1 (1 - p.2.val / 2) • p.1.val‖ = _
  rw [norm_smul, hmin, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - p.2.val / 2),
    mem_sphere_zero_iff_norm.mp p.1.2, mul_one]

lemma seamBallSnd_norm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (h : p.2.val ≤ 0) : ‖(seamBallSnd φ p).val‖ = 1 + p.2.val / 2 := by
  have ht : (-1 : ℝ) ≤ p.2.val := p.2.2.1
  have hmin : min 1 (1 + p.2.val / 2) = 1 + p.2.val / 2 := min_eq_right (by linarith)
  show ‖min 1 (1 + p.2.val / 2) • (φ p.1).val‖ = _
  rw [norm_smul, hmin, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + p.2.val / 2),
    mem_sphere_zero_iff_norm.mp (φ p.1).2, mul_one]

lemma norm_lowerRefl_eq_one_iff (y : lowerHemisphere m) :
    ‖(lowerHemisphereHomeoDiskRefl y).val‖ = 1 ↔ y.val.val 0 = 0 := by
  have h : (lowerHemisphereHomeoDiskRefl y) =
      hemisphereToDisk (lowerHomeoUpperRefl y) := rfl
  rw [h, norm_hemisphereToDisk_eq_one_iff]
  show reflectFirst y.val.val 0 = 0 ↔ _
  rw [reflectFirst_zero, neg_eq_zero]

lemma norms_eq_one_of_glue_eq
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (a b : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (h : (Quot.mk (GlueRel φ) (Sum.inl a) : TwistedSphere φ) = Quot.mk _ (Sum.inr b)) :
    ‖a.val‖ = 1 ∧ ‖b.val‖ = 1 := by
  have hval : (upperHemisphereHomeoDisk.symm a).val =
      (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm b)).val :=
    congrArg (twistedGlueToSphere φ) h
  have hzero : (upperHemisphereHomeoDisk.symm a).val.val 0 = 0 := by
    have h1 : (0 : ℝ) ≤ (upperHemisphereHomeoDisk.symm a).val.val 0 :=
      (upperHemisphereHomeoDisk.symm a).2
    have h2 : (upperHemisphereHomeoDisk.symm a).val.val 0 ≤ 0 := by
      rw [hval]
      exact (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm b)).2
    linarith
  constructor
  · have hh := (norm_hemisphereToDisk_eq_one_iff (upperHemisphereHomeoDisk.symm a)).mpr hzero
    have heq : hemisphereToDisk (upperHemisphereHomeoDisk.symm a) = a :=
      upperHemisphereHomeoDisk.apply_symm_apply a
    rwa [heq] at hh
  · have hzero' : (lowerHemisphereHomeoDiskRefl.symm
        (alexanderExt φ.symm b)).val.val 0 = 0 := by rw [← hval]; exact hzero
    have hh := (norm_lowerRefl_eq_one_iff
      (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm b))).mpr hzero'
    rw [lowerHemisphereHomeoDiskRefl.apply_symm_apply, alexanderExt_norm] at hh
    exact hh

lemma seamMap_of_nonneg
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (h : 0 ≤ p.2.val) :
    seamMap φ p = Quot.mk _ (Sum.inl (seamBallFst p)) := by
  simp only [seamMap]
  exact if_pos h

lemma seamMap_of_neg
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1)
    (h : ¬ (0 ≤ p.2.val)) :
    seamMap φ p = Quot.mk _ (Sum.inr (seamBallSnd φ p)) := by
  simp only [seamMap]
  exact if_neg h

lemma injective_seamMap
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Injective (seamMap φ) := by
  intro p q h
  by_cases hs : (0 : ℝ) ≤ p.2.val
  · by_cases ht : (0 : ℝ) ≤ q.2.val
    · 
      rw [seamMap_of_nonneg φ p hs, seamMap_of_nonneg φ q ht] at h
      have hball : seamBallFst p = seamBallFst q :=
        upperHemisphereHomeoDisk.symm.injective
          (Subtype.ext (congrArg (twistedGlueToSphere φ) h))
      have hn : ‖(seamBallFst p).val‖ = ‖(seamBallFst q).val‖ := by rw [hball]
      rw [seamBallFst_norm _ hs, seamBallFst_norm _ ht] at hn
      have hst : p.2.val = q.2.val := by linarith
      have hpos : (0 : ℝ) < min 1 (1 - p.2.val / 2) :=
        lt_min one_pos (by have := p.2.2.2; linarith)
      have hvec : min 1 (1 - p.2.val / 2) • p.1.val =
          min 1 (1 - q.2.val / 2) • q.1.val := congrArg Subtype.val hball
      rw [← hst] at hvec
      exact Prod.ext (Subtype.ext (smul_right_injective _ (ne_of_gt hpos) hvec))
        (Subtype.ext hst)
    · 
      exfalso
      rw [seamMap_of_nonneg φ p hs, seamMap_of_neg φ q ht] at h
      have hb := (norms_eq_one_of_glue_eq φ _ _ h).2
      rw [seamBallSnd_norm φ _ (le_of_lt (lt_of_not_ge ht))] at hb
      have := lt_of_not_ge ht
      linarith
  · by_cases ht : (0 : ℝ) ≤ q.2.val
    · 
      exfalso
      rw [seamMap_of_neg φ p hs, seamMap_of_nonneg φ q ht] at h
      have hb := (norms_eq_one_of_glue_eq φ _ _ h.symm).2
      rw [seamBallSnd_norm φ _ (le_of_lt (lt_of_not_ge hs))] at hb
      have := lt_of_not_ge hs
      linarith
    · 
      rw [seamMap_of_neg φ p hs, seamMap_of_neg φ q ht] at h
      have hball : seamBallSnd φ p = seamBallSnd φ q := by
        have hval : (lowerHemisphereHomeoDiskRefl.symm
            (alexanderExt φ.symm (seamBallSnd φ p))).val =
            (lowerHemisphereHomeoDiskRefl.symm
              (alexanderExt φ.symm (seamBallSnd φ q))).val :=
          congrArg (twistedGlueToSphere φ) h
        have h2 : alexanderExt φ.symm (seamBallSnd φ p) =
            alexanderExt φ.symm (seamBallSnd φ q) :=
          lowerHemisphereHomeoDiskRefl.symm.injective (Subtype.ext hval)
        have e1 : alexanderExt φ (alexanderExt φ.symm (seamBallSnd φ p)) =
            seamBallSnd φ p := by
          have hx := alexanderExt_symm_alexanderExt φ.symm (seamBallSnd φ p)
          rwa [Homeomorph.symm_symm] at hx
        have e2 : alexanderExt φ (alexanderExt φ.symm (seamBallSnd φ q)) =
            seamBallSnd φ q := by
          have hx := alexanderExt_symm_alexanderExt φ.symm (seamBallSnd φ q)
          rwa [Homeomorph.symm_symm] at hx
        rw [← e1, ← e2, h2]
      have hn : ‖(seamBallSnd φ p).val‖ = ‖(seamBallSnd φ q).val‖ := by rw [hball]
      rw [seamBallSnd_norm φ _ (le_of_lt (lt_of_not_ge hs)),
        seamBallSnd_norm φ _ (le_of_lt (lt_of_not_ge ht))] at hn
      have hst : p.2.val = q.2.val := by linarith
      have hpos : (0 : ℝ) < min 1 (1 + p.2.val / 2) :=
        lt_min one_pos (by have := p.2.2.1; linarith)
      have hvec : min 1 (1 + p.2.val / 2) • (φ p.1).val =
          min 1 (1 + q.2.val / 2) • (φ q.1).val := congrArg Subtype.val hball
      rw [← hst] at hvec
      have huv : (φ p.1).val = (φ q.1).val :=
        smul_right_injective _ (ne_of_gt hpos) hvec
      exact Prod.ext (φ.injective (Subtype.ext huv)) (Subtype.ext hst)

def openSeam
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Set (TwistedSphere φ) :=
  seamMap φ '' { p | -1 < p.2.val ∧ p.2.val < 1 }

lemma mem_openSeam_inl
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (Quot.mk (GlueRel φ) (Sum.inl w) : TwistedSphere φ) ∈ openSeam φ ↔
      1 / 2 < ‖w.val‖ := by
  constructor
  · rintro ⟨p, hp, hseam⟩
    by_cases hs : (0 : ℝ) ≤ p.2.val
    · rw [seamMap_of_nonneg φ p hs] at hseam
      have hb : seamBallFst p = w :=
        upperHemisphereHomeoDisk.symm.injective
          (Subtype.ext (congrArg (twistedGlueToSphere φ) hseam))
      rw [← hb, seamBallFst_norm p hs]
      linarith [hp.2]
    · rw [seamMap_of_neg φ p hs] at hseam
      have h1 := (norms_eq_one_of_glue_eq φ w _ hseam.symm).1
      rw [h1]; norm_num
  · intro hw
    have hle : ‖w.val‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
    have hne : w.val ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hw; linarith
    refine ⟨(unitOr diskNorth w.val, ⟨2 * (1 - ‖w.val‖), ⟨by linarith, by linarith⟩⟩),
      ⟨by simp only; linarith, by simp only; linarith⟩, ?_⟩
    rw [seamMap_of_nonneg φ _ (by simp only; linarith)]
    congr 1
    apply congrArg Sum.inl
    apply Subtype.ext
    show min 1 (1 - 2 * (1 - ‖w.val‖) / 2) • (unitOr diskNorth w.val).val = w.val
    have hr : 1 - 2 * (1 - ‖w.val‖) / 2 = ‖w.val‖ := by ring
    rw [hr, min_eq_right hle, smul_unitOr diskNorth hne]

lemma mem_openSeam_inr
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (Quot.mk (GlueRel φ) (Sum.inr w) : TwistedSphere φ) ∈ openSeam φ ↔
      1 / 2 < ‖w.val‖ := by
  constructor
  · rintro ⟨p, hp, hseam⟩
    by_cases hs : (0 : ℝ) ≤ p.2.val
    · rw [seamMap_of_nonneg φ p hs] at hseam
      have h1 := (norms_eq_one_of_glue_eq φ _ w hseam).2
      rw [h1]; norm_num
    · rw [seamMap_of_neg φ p hs] at hseam
      have hb : seamBallSnd φ p = w := by
        have hval : (lowerHemisphereHomeoDiskRefl.symm
            (alexanderExt φ.symm (seamBallSnd φ p))).val =
            (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w)).val :=
          congrArg (twistedGlueToSphere φ) hseam
        have h2 : alexanderExt φ.symm (seamBallSnd φ p) = alexanderExt φ.symm w :=
          lowerHemisphereHomeoDiskRefl.symm.injective (Subtype.ext hval)
        have e1 : alexanderExt φ (alexanderExt φ.symm (seamBallSnd φ p)) =
            seamBallSnd φ p := by
          have hx := alexanderExt_symm_alexanderExt φ.symm (seamBallSnd φ p)
          rwa [Homeomorph.symm_symm] at hx
        have e2 : alexanderExt φ (alexanderExt φ.symm w) = w := by
          have hx := alexanderExt_symm_alexanderExt φ.symm w
          rwa [Homeomorph.symm_symm] at hx
        rw [← e1, ← e2, h2]
      rw [← hb, seamBallSnd_norm φ p (le_of_lt (lt_of_not_ge hs))]
      linarith [hp.1]
  · intro hw
    have hle : ‖w.val‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
    have hne : w.val ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hw; linarith
    by_cases hone : ‖w.val‖ = 1
    · 
      refine ⟨(φ.symm (unitOr diskNorth w.val), ⟨0, ⟨by norm_num, by norm_num⟩⟩),
        ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [seamMap_of_nonneg φ _ (by simp only; norm_num)]
      have hfst : seamBallFst ((φ.symm (unitOr diskNorth w.val),
          ⟨0, ⟨by norm_num, by norm_num⟩⟩) :
            sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Set.Icc (-1 : ℝ) 1) =
          sphereToDisk (φ.symm (unitOr diskNorth w.val)) := by
        apply Subtype.ext
        show min 1 (1 - (0 : ℝ) / 2) • (φ.symm (unitOr diskNorth w.val)).val = _
        have hm : min 1 (1 - (0 : ℝ) / 2) = 1 := by norm_num
        rw [hm, one_smul]
        rfl
      rw [hfst]
      have hglue := Quot.sound (GlueRel.glue (φ := φ)
        (φ.symm (unitOr diskNorth w.val)))
      rw [hglue, Homeomorph.apply_symm_apply]
      congr 1
      apply congrArg Sum.inr
      apply Subtype.ext
      show (unitOr diskNorth w.val).val = w.val
      rw [unitOr_val_of_ne diskNorth hne, hone, inv_one, one_smul]
    · 
      refine ⟨(φ.symm (unitOr diskNorth w.val),
        ⟨-(2 * (1 - ‖w.val‖)), ⟨by linarith, by linarith⟩⟩),
        ⟨by simp only; linarith, by simp only; linarith⟩, ?_⟩
      have hneg : ¬ ((0 : ℝ) ≤ -(2 * (1 - ‖w.val‖))) := by
        have : ‖w.val‖ < 1 := lt_of_le_of_ne hle hone
        push_neg
        linarith
      rw [seamMap_of_neg φ _ (by simp only; exact hneg)]
      congr 1
      apply congrArg Sum.inr
      apply Subtype.ext
      show min 1 (1 + -(2 * (1 - ‖w.val‖)) / 2) •
        (φ (φ.symm (unitOr diskNorth w.val))).val = w.val
      rw [Homeomorph.apply_symm_apply]
      have hr : 1 + -(2 * (1 - ‖w.val‖)) / 2 = ‖w.val‖ := by ring
      rw [hr, min_eq_right hle, smul_unitOr diskNorth hne]

end Hemisphere

end SP4Seam


