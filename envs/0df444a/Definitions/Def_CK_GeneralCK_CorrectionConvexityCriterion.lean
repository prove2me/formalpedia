-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionConvexityCriterion
-- name    : CK_GeneralCK_CorrectionConvexityCriterion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:03.840318+00:00
-- url     : https://prove2.me/theorems/ee019d76-7347-4187-8f80-e2e2bccada37
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionConvexityCriterion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionConvexityCriterion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionConvexityCriterion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionConvexityCriterion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionConvexityCriterion.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHessianPSD
import Definitions.Def_CK_GeneralCK_PerspectiveCurve
import Mathlib.Analysis.Convex.Deriv

namespace GeneralCK.Correction
open Set Filter
open scoped Topology

def orderedTriangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}

noncomputable def curveSlope (e f a b : ℝ) : ℝ :=
  ((b*invSlope f-a*invSlope e)*(J (entropyInverse e)-J (entropyInverse f))+
    gap e f*(a*jSlope e-b*jSlope f))/2 -
  perspectiveSlope (gap e f) (mid e f) (b*invSlope f-a*invSlope e) ((a+b)/2)

theorem hasDerivAt_correction_curve {E G : ℝ → ℝ} {x a b : ℝ}
    (hE : HasDerivAt E a x) (hG : HasDerivAt G b x)
    (he : 0 < E x) (hef : E x < G x) (hf : G x < 1) :
    HasDerivAt (fun t => entropyCorrection (E t) (G t))
      (curveSlope (E x) (G x) a b) x := by
  have hiE := (hasDerivAt_entropyInverse he (hef.trans hf)).comp x hE
  have hiG := (hasDerivAt_entropyInverse (he.trans hef) hf).comp x hG
  have hjE := (hasDerivAt_entropyJ he (hef.trans hf)).comp x hE
  have hjG := (hasDerivAt_entropyJ (he.trans hef) hf).comp x hG
  have hs := hiG.sub hiE
  have hm := (hE.add hG).div_const 2
  have hdF := hasDerivAt_F_curve hs hm (gap_pos he hef hf) (mid_pos he hef)
  have hd := ((hs.mul (hjE.sub hjG)).div_const 2).sub hdF
  have heq : (fun t => entropyCorrection (E t) (G t)) =ᶠ[𝓝 x]
      (fun t => (entropyInverse (G t)-entropyInverse (E t))*
        (J (entropyInverse (E t))-J (entropyInverse (G t)))/2-
        F (entropyInverse (G t)-entropyInverse (E t)) ((E t+G t)/2)) := by
    filter_upwards [hE.continuousAt.eventually (Ioi_mem_nhds he),
      (hG.continuousAt.sub hE.continuousAt).eventually (Ioi_mem_nhds (sub_pos.mpr hef)),
      hG.continuousAt.eventually (Iio_mem_nhds hf)] with t ht htg htf
    rw [ordered_eq ht (sub_pos.mp htg) htf]
    dsimp [ordered, gap, normalized, mid]
    dsimp at htg
    rw [F_perspective (by linarith : (E t+G t)/2 ≠ 0)]
  convert! hd.congr_of_eventuallyEq heq using 1
  dsimp [curveSlope, invSlope, perspectiveSlope, gap, mid]
  ring

theorem hasDerivAt_curveSlope {E G : ℝ → ℝ} {x a b : ℝ}
    (hE : HasDerivAt E a x) (hG : HasDerivAt G b x)
    (he : 0 < E x) (hef : E x < G x) (hf : G x < 1) :
    HasDerivAt (fun t => curveSlope (E t) (G t) a b)
      (hessianLL (E x) (G x)*a^2+2*hessianLR (E x) (G x)*a*b+
        hessianRR (E x) (G x)*b^2) x := by
  have hiE := (hasDerivAt_entropyInverse he (hef.trans hf)).comp x hE
  have hiG := (hasDerivAt_entropyInverse (he.trans hef) hf).comp x hG
  have hsE := (hasDerivAt_invSlope he (hef.trans hf)).comp x hE
  have hsG := (hasDerivAt_invSlope (he.trans hef) hf).comp x hG
  have hjE := (hasDerivAt_entropyJ he (hef.trans hf)).comp x hE
  have hjG := (hasDerivAt_entropyJ (he.trans hef) hf).comp x hG
  have hjsE := (hasDerivAt_jSlope he (hef.trans hf)).comp x hE
  have hjsG := (hasDerivAt_jSlope (he.trans hef) hf).comp x hG
  have hs : HasDerivAt (fun t => gap (E t) (G t))
      (b*invSlope (G x)-a*invSlope (E x)) x := by
    convert! hiG.sub hiE using 1
    dsimp [invSlope]
    ring
  have hm := (hE.add hG).div_const 2
  have hds := (hsG.const_mul b).sub (hsE.const_mul a)
  have hdF := hasDerivAt_perspectiveSlope
    (s := fun t => gap (E t) (G t)) (e := fun t => mid (E t) (G t))
    (ds := fun t => b*invSlope (G t)-a*invSlope (E t)) (de := fun _ => (a+b)/2)
    hs hm hds (hasDerivAt_const x ((a+b)/2))
    (gap_pos he hef hf) (mid_pos he hef)
  have hcost := ((hds.mul (hjE.sub hjG)).add
    (hs.mul ((hjsE.const_mul a).sub (hjsG.const_mul b)))).div_const 2
  have hd := hcost.sub hdF
  convert! hd using 1
  dsimp [hessianLL, hessianLR, hessianRR, costLL, costLR, costRR,
    normalized, mid, gap, invSlope]
  ring


noncomputable def affine (u a t : ℝ) : ℝ := u+t*a

theorem hasDerivAt_affine (u a t : ℝ) : HasDerivAt (affine u a) a t := by
  convert! ((hasDerivAt_id t).mul_const a).const_add u using 1
  simp

theorem hasDerivAt_deriv_correction_affine {u v a b t : ℝ}
    (he : 0 < affine u a t) (hef : affine u a t < affine v b t)
    (hf : affine v b t < 1) :
    HasDerivAt (deriv (fun s => entropyCorrection (affine u a s) (affine v b s)))
      (hessianQuadratic (affine u a t) (affine v b t) a b) t := by
  have hE := hasDerivAt_affine u a t
  have hG := hasDerivAt_affine v b t
  have hd := hasDerivAt_curveSlope hE hG he hef hf
  have heq : deriv (fun s => entropyCorrection (affine u a s) (affine v b s)) =ᶠ[𝓝 t]
      (fun s => curveSlope (affine u a s) (affine v b s) a b) := by
    filter_upwards [hE.continuousAt.eventually (Ioi_mem_nhds he),
      (hG.continuousAt.sub hE.continuousAt).eventually (Ioi_mem_nhds (sub_pos.mpr hef)),
      hG.continuousAt.eventually (Iio_mem_nhds hf)] with s hs hsg hsf
    exact (hasDerivAt_correction_curve (hasDerivAt_affine u a s) (hasDerivAt_affine v b s)
      hs (sub_pos.mp hsg) hsf).deriv
  convert! hd.congr_of_eventuallyEq heq using 1
  unfold hessianQuadratic
  rw [(hasDerivAt_deriv_entropyCorrection_left he hef hf).deriv,
    (hasDerivAt_entropyCorrection_left_right he hef hf).deriv,
    (hasDerivAt_deriv_entropyCorrection_right he hef hf).deriv]

private theorem combo_pos {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : 0 < a*x+b*y := by
  rcases lt_or_eq_of_le ha with ha | ha
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb hy.le)
  · have ha0 : a=0 := ha.symm
    have hb1 : b=1 := by linarith
    simpa [ha0, hb1] using hy

theorem orderedTriangle_convex : Convex ℝ orderedTriangle := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx, hxy, hx1⟩
  rcases hy with ⟨hy, hyz, hy1⟩
  change 0 < a*x.1+b*y.1 ∧ a*x.1+b*y.1 < a*x.2+b*y.2 ∧ a*x.2+b*y.2 < 1
  refine ⟨combo_pos hx hy ha hb hab, ?_, ?_⟩
  · have := combo_pos (sub_pos.mpr hxy) (sub_pos.mpr hyz) ha hb hab
    nlinarith
  · have := combo_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1) ha hb hab
    nlinarith

theorem affine_segment_mem {x y : ℝ × ℝ} (hx : x ∈ orderedTriangle)
    (hy : y ∈ orderedTriangle) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (affine x.1 (y.1-x.1) t, affine x.2 (y.2-x.2) t) ∈ orderedTriangle := by
  have hp := orderedTriangle_convex hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  convert! hp using 1
  ext <;> dsimp [affine] <;> ring

/-- Convexity on the ordered open triangle requires only the two pointwise source minors. -/
theorem convexOn_entropyCorrection_of_minors
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :
    ConvexOn ℝ orderedTriangle (fun p => entropyCorrection p.1 p.2) := by
  refine ⟨orderedTriangle_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let E := affine x.1 (y.1-x.1)
  let G := affine x.2 (y.2-x.2)
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      0 < E t ∧ E t < G t ∧ G t < 1 := affine_segment_mem hx hy ht
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) (fun t => entropyCorrection (E t) (G t)) := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc 0 1)
    · intro t ht
      obtain ⟨he, hef, hf⟩ := hmem t ht
      exact (hasDerivAt_correction_curve (hasDerivAt_affine _ _ _) (hasDerivAt_affine _ _ _)
        he hef hf).differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨he, hef, hf⟩ := hmem t ht
      exact (hasDerivAt_deriv_correction_affine he hef hf).differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨he, hef, hf⟩ := hmem t ht
      change 0 ≤ deriv (deriv (fun s => entropyCorrection (E s) (G s))) t
      rw [(hasDerivAt_deriv_correction_affine he hef hf).deriv]
      exact hessianQuadratic_nonneg he hef hf
        (hleft (E t, G t) ⟨he, hef, hf⟩) (hdet (E t, G t) ⟨he, hef, hf⟩) _ _
  have hc := hconv.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num) ha hb hab
  have heqE : E (a*0+b*1) = a*x.1+b*y.1 := by
    dsimp [E, affine]
    rw [show a=1-b by linarith]
    ring
  have heqG : G (a*0+b*1) = a*x.2+b*y.2 := by
    dsimp [G, affine]
    rw [show a=1-b by linarith]
    ring
  change entropyCorrection (a*x.1+b*y.1) (a*x.2+b*y.2) ≤
    a*entropyCorrection x.1 x.2+b*entropyCorrection y.1 y.2
  simpa only [smul_eq_mul, heqE, heqG, E, G, affine, zero_mul, add_zero,
    one_mul, add_sub_cancel, Prod.fst_add, Prod.snd_add, Prod.fst_smul, Prod.snd_smul] using hc

end GeneralCK.Correction


