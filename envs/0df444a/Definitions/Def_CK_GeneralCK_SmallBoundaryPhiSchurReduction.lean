-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiSchurReduction
-- name    : CK_GeneralCK_SmallBoundaryPhiSchurReduction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:33:59.01891+00:00
-- url     : https://prove2.me/theorems/e7898cfa-258d-451f-ac0b-2040027156cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiSchurReduction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiSchurReduction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiSchurReduction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiSchurReduction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiSchurReduction.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff
import Definitions.Def_CK_GeneralCK_CorrectionConvexityCriterion

-- ===== source module GeneralCK.SmallBoundaryPhiSchurReduction =====
section

/-!
# SB-1 reduced to one scalar Schur-complement inequality

The positive entropy Hessian entry is already known. This module proves the
actual affine-path Hessian identity and consumes only its remaining scalar
Schur complement. Every scalar sign premise below remains explicit.
-/

namespace GeneralCK.SmallBoundaryPhiSchur

open Set Filter
open scoped Topology
open SmallMeanPhiCutoff

set_option maxHeartbeats 800000

def domain : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ retainedCutoff ∧ 0 < p.2 ∧ p.2 ≤ H p.1}

noncomputable def adjusted (m h : ℝ) : ℝ := phi m h - 4 * H m
noncomputable def radiusCurvature (m h : ℝ) : ℝ :=
  deriv (deriv (fun z => F z h)) (1 - 2*m)
noncomputable def entropyEntry (m h : ℝ) : ℝ :=
  Scalar.etaCurvature h - ((1-2*m)/h)^2 * radiusCurvature m h
noncomputable def schurNumerator (m h : ℝ) : ℝ :=
  entropyEntry m h / (Real.log 2*m*(1-m)) -
    radiusCurvature m h * Scalar.etaCurvature h
noncomputable def quadratic (m h x y : ℝ) : ℝ :=
  Scalar.etaCurvature h*y^2 - radiusCurvature m h*(-2*x-(1-2*m)/h*y)^2 +
    4/(Real.log 2*m*(1-m))*x^2
noncomputable def curveSlope (m h x y : ℝ) : ℝ :=
  deriv eta h*y - perspectiveSlope (1-2*m) h (-2*x) y - 4*J m*x

/-- One scalar inequality on exactly the smaller domain needed by SB-1. -/
def ScalarCurvatureOwner : Prop :=
  ∀ p ∈ domain, 0 ≤ schurNumerator p.1 p.2

theorem domain_bounds {m h : ℝ} (hp : (m,h) ∈ domain) :
    0 < m ∧ m < 1/2 ∧ 0 < h ∧ h < 1 := by
  have hm : m < 1/2 := by
    have hu := hp.2.1
    dsimp [retainedCutoff] at hu
    linarith
  refine ⟨hp.1, hm, hp.2.2.1, hp.2.2.2.trans_lt ?_⟩
  simpa only [H_half] using
    H_strictMonoOn ⟨hp.1.le, hm.le⟩ ⟨by norm_num, le_rfl⟩ hm

theorem entropyEntry_pos {m h : ℝ} (hp : (m,h) ∈ domain) :
    0 < entropyEntry m h := by
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  have hs : 0 < 1-2*m := by linarith
  have hs' : 1-2*m < 1 := by linarith
  have hcap : h ≤ H ((1-(1-2*m))/2) := by
    rw [show (1-(1-2*m))/2=m by ring]
    exact hp.2.2.2
  have hc := deriv2_radialPhi_entropy_pos hs hs' hh hcap
  rw [EntropyCurvature.deriv2_radialPhi_entropy hs hh hh',
    deriv2_F_entropy hs hh] at hc
  exact hc

theorem quadratic_nonneg {m h : ℝ} (hp : (m,h) ∈ domain)
    (hc : 0 ≤ schurNumerator m h) (x y : ℝ) : 0 ≤ quadratic m h x y := by
  have hpos := entropyEntry_pos hp
  have hdet : 0 ≤ entropyEntry m h *
      (4/(Real.log 2*m*(1-m))-4*radiusCurvature m h) -
      (-2*((1-2*m)/h)*radiusCurvature m h)^2 := by
    have heq : entropyEntry m h *
        (4/(Real.log 2*m*(1-m))-4*radiusCurvature m h) -
        (-2*((1-2*m)/h)*radiusCurvature m h)^2 = 4*schurNumerator m h := by
      dsimp [entropyEntry, schurNumerator]
      ring
    rw [heq]
    positivity
  have hn := Correction.quadratic_nonneg_of_minor hpos hdet (x := y) (y := x)
  convert hn using 1
  dsimp [quadratic, entropyEntry]
  ring

theorem hasDerivAt_adjusted_curve {M E : ℝ → ℝ} {t x y : ℝ}
    (hM : HasDerivAt M x t) (hE : HasDerivAt E y t)
    (hm : 0 < M t) (hm' : M t < 1/2) (he : 0 < E t) (he' : E t < 1) :
    HasDerivAt (fun u => adjusted (M u) (E u))
      (curveSlope (M t) (E t) x y) t := by
  have hrad : HasDerivAt (fun u => 1-2*M u) (-2*x) t := by
    convert! (hM.const_mul 2).const_sub 1 using 1
    ring
  have heta := ((hasDerivAt_eta he he').differentiableAt.hasDerivAt).comp t hE
  have hF := hasDerivAt_F_curve hrad hE (by linarith) he
  have hH := (Comparison.hasDerivAt_H hm (by linarith)).comp t hM
  have hd := (heta.sub hF).sub (hH.const_mul 4)
  have heq : (fun u => adjusted (M u) (E u)) =ᶠ[𝓝 t]
      (fun u => eta (E u)-F (1-2*M u) (E u)-4*H (M u)) := by
    filter_upwards [hM.continuousAt.eventually (Iio_mem_nhds hm')] with u hu
    dsimp [adjusted, phi]
    rw [abs_of_pos (by linarith)]
  convert! hd.congr_of_eventuallyEq heq using 1
  dsimp [curveSlope]
  ring

theorem hasDerivAt_curveSlope {M E : ℝ → ℝ} {t x y : ℝ}
    (hM : HasDerivAt M x t) (hE : HasDerivAt E y t)
    (hm : 0 < M t) (hm' : M t < 1/2) (he : 0 < E t) (he' : E t < 1) :
    HasDerivAt (fun u => curveSlope (M u) (E u) x y)
      (quadratic (M t) (E t) x y) t := by
  have hs : 0 < 1-2*M t := by linarith
  have hrad : HasDerivAt (fun u => 1-2*M u) (-2*x) t := by
    convert! (hM.const_mul 2).const_sub 1 using 1
    ring
  have heta := ((Scalar.hasDerivAt_deriv_eta he he').comp t hE).mul_const y
  have hF := hasDerivAt_perspectiveSlope (ds := fun _ => -2*x) (de := fun _ => y)
    hrad hE (hasDerivAt_const t _) (hasDerivAt_const t _) hs he
  have hJ := (((hasDerivAt_J hm (by linarith)).comp t hM).const_mul 4).mul_const x
  have hd := (heta.sub hF).sub hJ
  convert! hd using 1
  dsimp [quadratic, radiusCurvature]
  rw [deriv2_F_radius_normalize hs he]
  ring

theorem hasDerivAt_deriv_adjusted_affine {u v x y t : ℝ}
    (hm : 0 < Correction.affine u x t) (hm' : Correction.affine u x t < 1/2)
    (he : 0 < Correction.affine v y t) (he' : Correction.affine v y t < 1) :
    HasDerivAt (deriv (fun z => adjusted (Correction.affine u x z) (Correction.affine v y z)))
      (quadratic (Correction.affine u x t) (Correction.affine v y t) x y) t := by
  have hM := Correction.hasDerivAt_affine u x t
  have hE := Correction.hasDerivAt_affine v y t
  have hd := hasDerivAt_curveSlope hM hE hm hm' he he'
  have heq : deriv (fun z => adjusted (Correction.affine u x z) (Correction.affine v y z))
      =ᶠ[𝓝 t] (fun z => curveSlope (Correction.affine u x z) (Correction.affine v y z) x y) := by
    filter_upwards [hM.continuousAt.eventually (Ioo_mem_nhds hm hm'),
      hE.continuousAt.eventually (Ioo_mem_nhds he he')] with z hz hz'
    exact (hasDerivAt_adjusted_curve (Correction.hasDerivAt_affine _ _ _)
      (Correction.hasDerivAt_affine _ _ _) hz.1 hz.2 hz'.1 hz'.2).deriv
  exact hd.congr_of_eventuallyEq heq

private theorem combo_pos {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : 0 < a*x+b*y := by
  rcases lt_or_eq_of_le ha with ha | ha
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb hy.le)
  · have ha0 : a=0 := ha.symm
    have hb1 : b=1 := by linarith
    simpa [ha0,hb1] using hy

theorem domain_convex : Convex ℝ domain := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hm, hm', _, _⟩ := domain_bounds hp
  obtain ⟨hn, hn', _, _⟩ := domain_bounds hq
  have hH := H_concaveOn_unit.2 (show p.1 ∈ Icc 0 1 from ⟨hm.le, by linarith⟩)
    (show q.1 ∈ Icc 0 1 from ⟨hn.le, by linarith⟩) ha hb hab
  change a*H p.1+b*H q.1 ≤ H (a*p.1+b*q.1) at hH
  change 0 < a*p.1+b*q.1 ∧ a*p.1+b*q.1 ≤ retainedCutoff ∧
    0 < a*p.2+b*q.2 ∧ a*p.2+b*q.2 ≤ H (a*p.1+b*q.1)
  refine ⟨combo_pos hp.1 hq.1 ha hb hab, ?_, combo_pos hp.2.2.1 hq.2.2.1 ha hb hab, ?_⟩
  · calc
      a*p.1+b*q.1 ≤ a*retainedCutoff+b*retainedCutoff :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2.1 ha)
          (mul_le_mul_of_nonneg_left hq.2.1 hb)
      _ = retainedCutoff := by rw [← add_mul, hab, one_mul]
  · exact (add_le_add (mul_le_mul_of_nonneg_left hp.2.2.2 ha)
      (mul_le_mul_of_nonneg_left hq.2.2.2 hb)).trans hH

theorem affine_segment_mem {p q : ℝ × ℝ} (hp : p ∈ domain) (hq : q ∈ domain)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (Correction.affine p.1 (q.1-p.1) t, Correction.affine p.2 (q.2-p.2) t) ∈ domain := by
  have hc := domain_convex hp hq (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  convert! hc using 1
  ext <;> dsimp [Correction.affine] <;> ring

theorem convexOn_adjusted_of_scalarCurvature (h : ScalarCurvatureOwner) :
    ConvexOn ℝ domain (fun p => adjusted p.1 p.2) := by
  refine ⟨domain_convex, ?_⟩
  intro p hp q hq a b ha hb hab
  let M := Correction.affine p.1 (q.1-p.1)
  let E := Correction.affine p.2 (q.2-p.2)
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (M t,E t) ∈ domain :=
    affine_segment_mem hp hq ht
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) (fun t => adjusted (M t) (E t)) := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc 0 1)
    · intro t ht
      obtain ⟨hm, hm', he, he'⟩ := domain_bounds (hmem t ht)
      exact (hasDerivAt_adjusted_curve (Correction.hasDerivAt_affine _ _ _)
        (Correction.hasDerivAt_affine _ _ _) hm hm' he he').differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨hm, hm', he, he'⟩ := domain_bounds (hmem t ht)
      exact (hasDerivAt_deriv_adjusted_affine (u := p.1) (v := p.2)
        (x := q.1-p.1) (y := q.2-p.2) hm hm' he he').differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨hm, hm', he, he'⟩ := domain_bounds (hmem t ht)
      change 0 ≤ deriv (deriv (fun u => adjusted (M u) (E u))) t
      have hd : HasDerivAt (deriv (fun u => adjusted (M u) (E u)))
          (quadratic (M t) (E t) (q.1-p.1) (q.2-p.2)) t :=
        hasDerivAt_deriv_adjusted_affine (u := p.1) (v := p.2)
          (x := q.1-p.1) (y := q.2-p.2) hm hm' he he'
      rw [hd.deriv]
      exact quadratic_nonneg (m := M t) (h := E t) (hmem t ht)
        (h (M t,E t) (hmem t ht)) (q.1-p.1) (q.2-p.2)
  have hv := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num) ha hb hab
  have heqM : M (a*0+b*1) = a*p.1+b*q.1 := by
    dsimp [M, Correction.affine]
    rw [show a=1-b by linarith]
    ring
  have heqE : E (a*0+b*1) = a*p.2+b*q.2 := by
    dsimp [E, Correction.affine]
    rw [show a=1-b by linarith]
    ring
  change adjusted (a*p.1+b*q.1) (a*p.2+b*q.2) ≤
    a*adjusted p.1 p.2+b*adjusted q.1 q.2
  simpa only [smul_eq_mul, heqM, heqE, M, E, Correction.affine, zero_mul,
    add_zero, one_mul, add_sub_cancel, Prod.fst_add, Prod.snd_add,
    Prod.fst_smul, Prod.snd_smul] using hv

theorem smallBoundaryMidpoint_of_scalarCurvature (h : ScalarCurvatureOwner) :
    SmallBoundaryPhiMidpointOwner := by
  intro a b e f ha hab hs he hf hecap hfcap
  have hb : 0 < b := ha.trans_le hab
  have hap : (a,e) ∈ domain := ⟨ha, by linarith, he, hecap⟩
  have hbp : (b,f) ∈ domain := ⟨hb, by linarith, hf, hfcap⟩
  have hc := (convexOn_adjusted_of_scalarCurvature h).2 hap hbp
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  change adjusted ((1/2)*a+(1/2)*b) ((1/2)*e+(1/2)*f) ≤
    (1/2)*adjusted a e+(1/2)*adjusted b f at hc
  rw [show (1/2:ℝ)*a+(1/2)*b=(a+b)/2 by ring,
    show (1/2:ℝ)*e+(1/2)*f=(e+f)/2 by ring] at hc
  dsimp [adjusted] at hc
  unfold candidateGap
  linarith

theorem belowCutoffHybrid_of_scalarCurvature (h : ScalarCurvatureOwner) :
    BelowCutoffPhiHybridOwner :=
  belowCutoffHybrid_of_midpoint (smallBoundaryMidpoint_of_scalarCurvature h)

#print axioms entropyEntry_pos
#print axioms quadratic_nonneg
#print axioms hasDerivAt_adjusted_curve
#print axioms hasDerivAt_curveSlope
#print axioms hasDerivAt_deriv_adjusted_affine
#print axioms domain_convex
#print axioms affine_segment_mem
#print axioms convexOn_adjusted_of_scalarCurvature
#print axioms smallBoundaryMidpoint_of_scalarCurvature
#print axioms belowCutoffHybrid_of_scalarCurvature

end GeneralCK.SmallBoundaryPhiSchur

end


