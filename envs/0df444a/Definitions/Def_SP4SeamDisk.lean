-- Prove2me | Definitions.Def_SP4SeamDisk
-- name    : SP4SeamDisk
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T06:55:54.891378+00:00
-- url     : https://prove2.me/theorems/115c0656-cd62-4fa3-8757-05649c3a6ca9
-- title:
--   Disk smoothness and transported collar instances
-- statement:
--   For $m\geq0$, let $D^{m+1}=\{w\in\mathbb R^{m+1}:\|w\|\leq1\}$ and $S^m=\partial D^{m+1}$. Reuse the existing half-space disk charts. This bundle includes their smooth-manifold instance and the constructor support for the closed annulus $A_m=\{w\in D^{m+1}:1/2\leq\|w\|\}$. The collar homeomorphism is
--   $$c:S^m\times[0,1]\longrightarrow A_m,\qquad c(u,t)=(1-t/2)u.$$
--   The annulus charted-space and smooth-manifold instances are pulled back from the product sphere–interval structure along $c^{-1}$. They do not assert equality with a separately inherited smooth structure. The embedded analytic and collar lemmas support these instances; they are not additional public theorem targets or new SP4 claims.
-- source:
--   Ryan Shin, Disk.lean, unpublished Lean source (2026), selected constructor/instance support in lines 196–1384; supported-environment transcription SHA-256 bfbff246f588a3feb8f2990ac1c3a496c71f60b28eb8f37527a38638e0b8c5b0. Extracted by Lean compiler declaration/reference oracles, with namespace-only adaptations; no tracked source commit is claimed.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts
import Definitions.Def_SP4SeamPullbackGroupoid

set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph
open SP4Seam.Homeomorph

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

lemma contDiffOn_unitVector {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖⁻¹ • x)
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } := by
  intro x hx
  have h1 : ContDiffAt ℝ k (norm : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) x :=
    contDiffAt_norm (𝕜 := ℝ) hx
  exact ((h1.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt

lemma contDiffOn_boundaryAngular
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr
          (stereoToFun (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x))))
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x) ≠ (1 : ℝ) } := by
  refine ContDiff.comp_contDiffOn
    ((OrthonormalBasis.fromOrthogonalSpanSingleton m
      (ne_zero_of_mem_unit_sphere (-p))).repr.contDiff :
      ContDiff ℝ k _) ?_
  refine ContDiffOn.comp contDiffOn_stereoToFun
    (contDiffOn_unitVector.mono fun x hx => hx.1) ?_
  exact fun x hx => hx.2

lemma inner_unit_ne_one (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ≠ 0) (hp : unitOr p x ≠ -p) :
    innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x) ≠ (1 : ℝ) := by
  set q : EuclideanSpace ℝ (Fin (m + 1)) :=
    (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))) with hqdef
  set u : EuclideanSpace ℝ (Fin (m + 1)) := ‖x‖⁻¹ • x with hu
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hq : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp (-p).2
  intro h1
  have h2 : (inner ℝ q u : ℝ) = ‖q‖ * ‖u‖ := by
    rw [hq, hnu, one_mul]
    exact h1
  have h3 := inner_eq_norm_mul_iff.mp h2
  rw [hq, hnu] at h3
  simp only [RCLike.ofReal_one, one_smul] at h3
  apply hp
  ext1
  rw [unitOr_val_of_ne p hx, ← hu, ← h3]

lemma contDiffOn_oneSubNorm {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun x : EuclideanSpace ℝ (Fin (m + 1)) => 1 - ‖x‖)
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } :=
  fun _ hx => (contDiffAt_const.sub (contDiffAt_norm (𝕜 := ℝ) hx)).contDiffWithinAt

lemma contDiff_boundaryInv
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 - y 0) • stereoInvFunAux
        (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr.symm
          (WithLp.toLp 2 (Fin.tail (fun i => y i)))) :
            EuclideanSpace ℝ (Fin (m + 1))) + diskShift (m + 1)) := by
  have h0 : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) => 1 - y 0) := by
    refine contDiff_const.sub ?_
    exact ((ContinuousLinearMap.proj (0 : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
  have htail : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (WithLp.toLp 2 (Fin.tail (fun i => y i)) : EuclideanSpace ℝ (Fin m))) := by
    refine PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun j => ?_)
    exact ((ContinuousLinearMap.proj (j.succ : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
  have hrepr : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton m
          (ne_zero_of_mem_unit_sphere (-p))).repr.symm
        (WithLp.toLp 2 (Fin.tail (fun i => y i)))) :
          EuclideanSpace ℝ (Fin (m + 1)))) := by
    refine ((Submodule.subtypeL _ :
      _ →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).contDiff).comp ?_
    exact (((OrthonormalBasis.fromOrthogonalSpanSingleton m
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm.contDiff :
        ContDiff ℝ k _)).comp htail
  exact ((h0.smul ((contDiff_stereoInvFunAux (m := k)).comp hrepr)).add
    contDiff_const)

lemma contDiff_sphereLift
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr.symm
          (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
            EuclideanSpace ℝ (Fin (m + 1)))) := by
  have htail : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (WithLp.toLp 2 (Fin.tail (fun j => y j)) : EuclideanSpace ℝ (Fin m))) := by
    refine PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun j => ?_)
    exact ((ContinuousLinearMap.proj (j.succ : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
  refine (contDiff_stereoInvFunAux (m := k)).comp ?_
  refine ((Submodule.subtypeL _ :
    _ →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).contDiff).comp ?_
  exact (((OrthonormalBasis.fromOrthogonalSpanSingleton m
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm.contDiff :
      ContDiff ℝ k _)).comp htail

lemma contDiffOn_boundaryToBoundary
    (p p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (y 0)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p'))).repr
            (stereoToFun (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                  EuclideanSpace ℝ (Fin (m + 1)))
                (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
                  (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                    EuclideanSpace ℝ (Fin (m + 1)))))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { y : EuclideanSpace ℝ (Fin (m + 1)) |
        innerSL ℝ (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                (ne_zero_of_mem_unit_sphere (-p))).repr.symm
              (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                EuclideanSpace ℝ (Fin (m + 1)))) ≠ (1 : ℝ) } := by
  have hang : ContDiffOn ℝ k
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p'))).repr
          (stereoToFun (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                  (ne_zero_of_mem_unit_sphere (-p))).repr.symm
                (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                  EuclideanSpace ℝ (Fin (m + 1)))))))
      { y : EuclideanSpace ℝ (Fin (m + 1)) |
        innerSL ℝ (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                (ne_zero_of_mem_unit_sphere (-p))).repr.symm
              (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                EuclideanSpace ℝ (Fin (m + 1)))) ≠ (1 : ℝ) } := by
    refine ContDiff.comp_contDiffOn
      (((OrthonormalBasis.fromOrthogonalSpanSingleton m
        (ne_zero_of_mem_unit_sphere (-p'))).repr.contDiff : ContDiff ℝ k _)) ?_
    exact ContDiffOn.comp contDiffOn_stereoToFun
      (contDiff_sphereLift p).contDiffOn (fun y hy => hy)
  refine ContDiff.comp_contDiffOn PiLp.contDiff_toLp ?_
  refine contDiffOn_pi.mpr fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact (((ContinuousLinearMap.proj (0 : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp
        (PiLp.contDiff_ofLp (𝕜 := ℝ))).contDiffOn
  · simp only [Fin.cons_succ]
    exact ContDiff.comp_contDiffOn
      (((ContinuousLinearMap.proj (i : Fin m) :
        ((Fin m) → ℝ) →L[ℝ] ℝ).contDiff).comp (PiLp.contDiff_ofLp (𝕜 := ℝ)))
      hang

lemma contDiffOn_interiorToBoundaryFull
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (1 - ‖v - diskShift (m + 1)‖)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p))).repr
            (stereoToFun (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { v : EuclideanSpace ℝ (Fin (m + 1)) | v - diskShift (m + 1) ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
          (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))) ≠ (1 : ℝ) } := by
  have hshift : ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      v - diskShift (m + 1)) := contDiff_id.sub contDiff_const
  have hmapsto : Set.MapsTo (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      v - diskShift (m + 1))
      { v : EuclideanSpace ℝ (Fin (m + 1)) | v - diskShift (m + 1) ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
          (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))) ≠ (1 : ℝ) }
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x) ≠ (1 : ℝ) } :=
    fun v hv => hv
  refine ContDiff.comp_contDiffOn PiLp.contDiff_toLp ?_
  refine contDiffOn_pi.mpr fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact (contDiffOn_oneSubNorm.comp hshift.contDiffOn fun v hv => hv.1)
  · simp only [Fin.cons_succ]
    exact ContDiff.comp_contDiffOn
      (((ContinuousLinearMap.proj (i : Fin m) :
        ((Fin m) → ℝ) →L[ℝ] ℝ).contDiff).comp (PiLp.contDiff_ofLp (𝕜 := ℝ)))
      ((contDiffOn_boundaryAngular p).comp hshift.contDiffOn hmapsto)

set_option maxHeartbeats 800000 in
instance diskIsManifold {k : ℕ∞ω} :
    IsManifold (𝓡∂ (m + 1)) k
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
  rcases he with (rfl | ⟨p, rfl⟩) <;> rcases he' with (rfl | ⟨p', rfl⟩)
  · exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
  · refine ((contDiffOn_interiorToBoundaryFull p').mono ?_).congr ?_
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskInteriorChart,
        DiskBoundaryChart, modelWithCornersEuclideanHalfSpace,
        mfld_simps] at hz₁ hz₂
      have hupd : WithLp.toLp 2 (Function.update z.ofLp 0 (max (z.ofLp 0) 0)) = z := by
        rw [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      rw [hupd] at hz₁ hz₂
      rw [radialClamp_of_le _ hz₁.le] at hz₂
      exact ⟨hz₂.1, inner_unit_ne_one p' hz₂.1 (unitOr_ne_neg p' hz₂.1 hz₂.2)⟩
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskInteriorChart,
        DiskBoundaryChart, modelWithCornersEuclideanHalfSpace,
        mfld_simps] at hz₁ hz₂
      have hupd : WithLp.toLp 2 (Function.update z.ofLp 0 (max (z.ofLp 0) 0)) = z := by
        rw [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      rw [hupd] at hz₁ hz₂
      have hne : z - diskShift (m + 1) ≠ 0 := by
        have := hz₂.1
        rwa [radialClamp_of_le _ hz₁.le] at this
      simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply,
        ModelWithCorners.left_inv, DiskInteriorChart, DiskBoundaryChart,
        modelWithCornersEuclideanHalfSpace, mfld_simps]
      simp only [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      have harg : (⟨radialClamp (z - diskShift (m + 1)),
          mem_closedBall_zero_iff.mpr (norm_radialClamp_le _)⟩ :
            closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) =
          ⟨z - diskShift (m + 1), mem_closedBall_zero_iff.mpr hz₁.le⟩ :=
        Subtype.ext (radialClamp_of_le _ hz₁.le)
      rw [harg]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [DiskBoundaryChartFun]
      · simp [DiskBoundaryChartFun, unitOr_val_of_ne p' hne,
          stereographic', stereographic, stereoToFun, mfld_simps,
          map_sub, real_inner_smul_right, smul_smul, -coe_neg_sphere]
  · apply (contDiff_boundaryInv p).contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [OpenPartialHomeomorph.symm_symm, ModelWithCorners.left_inv,
      DiskInteriorChart, DiskBoundaryChart, modelWithCornersEuclideanHalfSpace,
      mfld_simps] at hz₁ hz₂
    simp only [Function.update_self, max_eq_left hz₀] at hz₁
    simp only [Function.comp_apply, ModelWithCorners.left_inv, DiskInteriorChart,
      DiskBoundaryChart, DiskBoundaryChartInv, modelWithCornersEuclideanHalfSpace,
      stereographic', stereographic, stereoInvFun, mfld_simps]
    simp only [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp,
      diskClamp_eq hz₀ hz₁.le]
    show (DiskBoundaryChartInv p ⟨z, hz₀⟩ : EuclideanSpace ℝ (Fin (m + 1))) +
      diskShift (m + 1) = _
    simp only [DiskBoundaryChartInv, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      stereographic', stereographic, stereoInvFun, mfld_simps]
    simp only [diskClamp_eq hz₀ hz₁.le]
    rfl
  · refine ((contDiffOn_boundaryToBoundary p p').mono ?_).congr ?_
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskBoundaryChart,
        modelWithCornersEuclideanHalfSpace, mfld_simps] at hz₁ hz₂
      simp only [Function.update_self, max_eq_left hz₀] at hz₁
      have hupd : WithLp.toLp 2 (Function.update z.ofLp 0 (max (z.ofLp 0) 0)) = z := by
        rw [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      simp only [hupd] at hz₂
      have hr : 0 < 1 - z.ofLp 0 := by linarith
      set u := (stereographic' m (-p)).symm
        (WithLp.toLp 2 (Fin.tail (fun i => z.ofLp i))) with hu
      have h22 : (0 ⊔ (1 ⊓ (1 - z.ofLp 0))) • (u : EuclideanSpace ℝ (Fin (m + 1))) ≠
          ‖(0 ⊔ (1 ⊓ (1 - z.ofLp 0))) • (u : EuclideanSpace ℝ (Fin (m + 1)))‖ •
            ((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1))) := hz₂.2
      rw [diskClamp_eq hz₀ hz₁.le] at h22
      have huval : ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp u.2
      have hnorm : ‖(1 - z.ofLp 0) • (u : EuclideanSpace ℝ (Fin (m + 1)))‖ =
          1 - z.ofLp 0 := by
        rw [norm_smul, huval, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      rw [hnorm] at h22
      have hne' : (u : EuclideanSpace ℝ (Fin (m + 1))) ≠
          ((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
        intro h
        apply h22
        conv_lhs => rw [h]
      intro h1
      have hq : ‖((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp (-p').2
      have h2 : (inner ℝ ((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (u : EuclideanSpace ℝ (Fin (m + 1))) : ℝ) =
          ‖((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))‖ * ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
        rw [hq, huval, one_mul]
        exact h1
      have h3 := inner_eq_norm_mul_iff.mp h2
      rw [hq, huval] at h3
      simp only [RCLike.ofReal_one, one_smul] at h3
      exact hne' h3.symm
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskBoundaryChart,
        modelWithCornersEuclideanHalfSpace, mfld_simps] at hz₁ hz₂
      simp only [Function.update_self, max_eq_left hz₀] at hz₁
      have hr : 0 < 1 - z.ofLp 0 := by linarith
      set u := (stereographic' m (-p)).symm
        (WithLp.toLp 2 (Fin.tail (fun i => z.ofLp i))) with hu
      have huval : ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp u.2
      have hnorm : ‖(1 - z.ofLp 0) • (u : EuclideanSpace ℝ (Fin (m + 1)))‖ =
          1 - z.ofLp 0 := by
        rw [norm_smul, huval, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      rw [Function.comp_apply, Function.comp_apply, ModelWithCorners.left_inv,
        OpenPartialHomeomorph.trans_apply]
      show (DiskBoundaryChartFun p' (DiskBoundaryChartInv p ⟨z, hz₀⟩)).val = _
      have hIv : ((DiskBoundaryChartInv p ⟨z, hz₀⟩) :
          EuclideanSpace ℝ (Fin (m + 1))) =
          (0 ⊔ (1 ⊓ (1 - z.ofLp 0))) • (u : EuclideanSpace ℝ (Fin (m + 1))) := rfl
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [DiskBoundaryChartFun_val_zero, hIv, diskClamp_eq hz₀ hz₁.le,
          hnorm, sub_sub_cancel, Fin.cons_zero, WithLp.ofLp_toLp,
          modelWithCornersEuclideanHalfSpace, mfld_simps]
      · simp only [DiskBoundaryChartFun_val_succ, hIv, diskClamp_eq hz₀ hz₁.le,
          unitOr_smul p' hr, stereographic', stereographic, Fin.cons_succ,
          WithLp.ofLp_toLp, modelWithCornersEuclideanHalfSpace, mfld_simps]
        rfl

end BoundaryChart

section BoundarySmooth

variable {m : ℕ}

end BoundarySmooth

section Collar

variable {m : ℕ}

def diskCollar (p : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ×
    (Set.Icc (0 : ℝ) 1)) :
    closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨(1 - p.2.val / 2) • p.1.val, by
    have h1 : ‖p.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have h2 : (0 : ℝ) ≤ 1 - p.2.val / 2 := by linarith [p.2.2.2]
    rw [mem_closedBall_zero_iff, norm_smul, h1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg h2]
    linarith [p.2.2.1]⟩

lemma continuous_diskCollar : Continuous (diskCollar (m := m)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub ((continuous_subtype_val.comp
    continuous_snd).div_const 2)).smul
    (continuous_subtype_val.comp continuous_fst))

lemma diskCollar_injective : Function.Injective (diskCollar (m := m)) := by
  rintro ⟨u, t⟩ ⟨v, s⟩ h
  have hval : (1 - t.val / 2) • u.val = (1 - s.val / 2) • v.val :=
    congrArg Subtype.val h
  have hnu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hnv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hpt : (0 : ℝ) < 1 - t.val / 2 := by linarith [t.2.2]
  have hps : (0 : ℝ) < 1 - s.val / 2 := by linarith [s.2.2]
  have hn := congrArg norm hval
  rw [norm_smul, norm_smul, hnu, hnv, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hpt, abs_of_pos hps] at hn
  have hts : t = s := Subtype.ext (by linarith)
  subst hts
  have huv : u.val = v.val :=
    smul_right_injective _ (ne_of_gt hpt) hval
  exact Prod.ext (Subtype.ext huv) rfl

theorem diskCollar_isClosedEmbedding :
    Topology.IsClosedEmbedding (diskCollar (m := m)) :=
  continuous_diskCollar.isClosedEmbedding diskCollar_injective

lemma range_diskCollar :
    Set.range (diskCollar (m := m)) =
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        1 / 2 ≤ ‖z.val‖ } := by
  ext z
  constructor
  · rintro ⟨⟨u, t⟩, rfl⟩
    have hnu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hpt : (0 : ℝ) ≤ 1 - t.val / 2 := by linarith [t.2.2]
    show 1 / 2 ≤ ‖(1 - t.val / 2) • u.val‖
    rw [norm_smul, hnu, mul_one, Real.norm_eq_abs, abs_of_nonneg hpt]
    linarith [t.2.2]
  · intro hz
    have hz' : (1 : ℝ) / 2 ≤ ‖z.val‖ := hz
    have hz1 : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
    have hzne : z.val ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz'
      linarith
    refine ⟨⟨unitOr diskNorth z.val,
      ⟨2 * (1 - ‖z.val‖), ⟨by linarith, by linarith [hz']⟩⟩⟩, ?_⟩
    apply Subtype.ext
    show (1 - (2 * (1 - ‖z.val‖)) / 2) • (unitOr diskNorth z.val).val = z.val
    have hr : 1 - (2 * (1 - ‖z.val‖)) / 2 = ‖z.val‖ := by ring
    rw [hr, smul_unitOr diskNorth hzne]

end Collar

section ValSmooth

variable {m : ℕ}

end ValSmooth

section Annulus

variable {m : ℕ}

def diskAnnulus (m : ℕ) : Set (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
  { z | 1 / 2 ≤ ‖z.val‖ }

noncomputable def diskCollarHomeo :
    ((sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) × (Set.Icc (0 : ℝ) 1)) ≃ₜ
      diskAnnulus m :=
  (diskCollar_isClosedEmbedding (m := m)).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_diskCollar)

noncomputable instance diskAnnulusChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanHalfSpace 1))
      (diskAnnulus m) :=
  (diskCollarHomeo (m := m)).symm.sp4MissionPullbackChartedSpace

instance diskAnnulusIsManifold {k : ℕ∞ω} :
    IsManifold ((𝓡 m).prod (𝓡∂ 1)) k (diskAnnulus m) := by
  have : HasGroupoid (diskAnnulus m) (contDiffGroupoid k ((𝓡 m).prod (𝓡∂ 1))) :=
    (diskCollarHomeo (m := m)).symm.sp4SeamPullbackHasGroupoid
      (contDiffGroupoid k ((𝓡 m).prod (𝓡∂ 1)))
  exact IsManifold.mk' _ _ _

end Annulus

end

end SP4Seam


