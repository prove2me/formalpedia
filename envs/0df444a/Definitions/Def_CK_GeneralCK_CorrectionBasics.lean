-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionBasics
-- name    : CK_GeneralCK_CorrectionBasics
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:42:01.850859+00:00
-- url     : https://prove2.me/theorems/7cc008a1-b755-427d-8f2c-9de29649d77f
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionBasics` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionBasics` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionBasics` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionBasics (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionBasics.lean)

import Definitions.Def_CK_GeneralCK_FourMomentDefs
import Definitions.Def_CK_GeneralCK_RadialConvexity
import Definitions.Def_CK_GeneralCK_PhiEntropyConvexity

namespace GeneralCK
open Set

theorem entropyInverse_continuousOn : ContinuousOn entropyInverse (Icc (0:ℝ) 1) := by
  let g : Icc (0:ℝ) 1 → Icc (0:ℝ) (1/2) := fun h =>
    ⟨entropyInverse h, (entropyInverse_spec h.property.1 h.property.2).1,
      (entropyInverse_spec h.property.1 h.property.2).2.1⟩
  have hg : Monotone g := by
    intro a b hab
    exact entropyInverse_mono a.property.1 b.property.2 hab
  have hs : Function.Surjective g := by
    intro v
    refine ⟨⟨H v, H_nonneg v.property.1 (by linarith [v.property.2]), H_le_one v⟩, ?_⟩
    apply Subtype.ext
    exact entropyInverse_H_lower v.property.1 v.property.2
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp (hg.continuous_of_surjective hs))

theorem F_continuousOn_positive_entropy :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Ici (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
  have hr : ContinuousOn (fun p : ℝ × ℝ => p.1/p.2) (Ici (0:ℝ) ×ˢ Ioi (0:ℝ)) :=
    continuous_fst.continuousOn.div continuous_snd.continuousOn (fun p hp => ne_of_gt hp.2)
  have hf := (continuousOn_F_radius (by norm_num : (0:ℝ)<1)).comp hr
    (fun p (hp : p ∈ Ici (0:ℝ) ×ˢ Ioi (0:ℝ)) =>
      show 0 ≤ p.1/p.2 from div_nonneg hp.1 (le_of_lt hp.2))
  apply (continuous_snd.continuousOn.mul hf).congr
  intro p hp
  exact F_perspective (ne_of_gt hp.2) p.1

theorem atomCorrection_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => atomCorrection p.1 p.2) (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
  have hj₁ : ContinuousOn (fun p : ℝ × ℝ => J p.1) (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
    intro p hp
    exact (hasDerivAt_J hp.1.1 hp.1.2).continuousAt.comp_continuousWithinAt continuous_fst.continuousWithinAt
  have hj₂ : ContinuousOn (fun p : ℝ × ℝ => J p.2) (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
    intro p hp
    exact (hasDerivAt_J hp.2.1 hp.2.2).continuousAt.comp_continuousWithinAt continuous_snd.continuousWithinAt
  have hc := ((continuous_snd.continuousOn.sub continuous_fst.continuousOn).mul (hj₁.sub hj₂)).div_const 2
  have hm : Continuous (fun p : ℝ × ℝ => (|p.1-p.2|,(H p.1+H p.2)/2)) := by
    exact ((continuous_fst.sub continuous_snd).abs).prodMk
      (((H_continuous.comp continuous_fst).add (H_continuous.comp continuous_snd)).div_const 2)
  have hf := F_continuousOn_positive_entropy.comp (hm.continuousOn (s := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) (by
    intro p hp
    change 0 ≤ |p.1-p.2| ∧ 0 < (H p.1+H p.2)/2
    exact ⟨abs_nonneg _, by have := H_pos hp.1.1 hp.1.2; have := H_pos hp.2.1 hp.2.2; positivity⟩)
  exact hc.sub hf

theorem entropyCorrection_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => entropyCorrection p.1 p.2) (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) := by
  have h₁ := entropyInverse_continuousOn.comp continuous_fst.continuousOn
    (fun p (hp : p ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) => ⟨hp.1.1.le,hp.1.2⟩)
  have h₂ := entropyInverse_continuousOn.comp continuous_snd.continuousOn
    (fun p (hp : p ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) => ⟨hp.2.1.le,hp.2.2⟩)
  exact atomCorrection_continuousOn.comp (h₁.prodMk h₂) (by
    intro p hp
    change (0 < entropyInverse p.1 ∧ entropyInverse p.1 < 1) ∧
      (0 < entropyInverse p.2 ∧ entropyInverse p.2 < 1)
    exact ⟨⟨entropyInverse_pos hp.1.1 hp.1.2, by linarith [(entropyInverse_spec hp.1.1.le hp.1.2).2.1]⟩,
      ⟨entropyInverse_pos hp.2.1 hp.2.2, by linarith [(entropyInverse_spec hp.2.1.le hp.2.2).2.1]⟩⟩)

theorem atomCorrection_comm (u v : ℝ) : atomCorrection u v = atomCorrection v u := by
  simp only [atomCorrection, interiorCost_comm u v, abs_sub_comm u v, add_comm]

theorem atomCorrection_complement (u v : ℝ) :
    atomCorrection (1-u) (1-v) = atomCorrection u v := by
  simp only [atomCorrection, interiorCost_complement, H_complement]
  rw [show 1-u-(1-v)=v-u by ring, abs_sub_comm v u]

theorem entropyCorrection_comm (e f : ℝ) : entropyCorrection e f = entropyCorrection f e :=
  atomCorrection_comm _ _

theorem entropyCorrection_of_lower_half {u v : ℝ} (hu : 0 < u) (hu' : u ≤ 1/2)
    (hv : 0 < v) (hv' : v ≤ 1/2) :
    entropyCorrection (H u) (H v) = atomCorrection u v := by
  simp only [entropyCorrection,entropyInverse_H_lower hu.le hu',entropyInverse_H_lower hv.le hv']

theorem entropyCorrection_nonneg_of_convex
    (hc : ConvexOn ℝ (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1)
      (fun p : ℝ × ℝ => entropyCorrection p.1 p.2))
    {e f : ℝ} (he : e ∈ Ioc (0:ℝ) 1) (hf : f ∈ Ioc (0:ℝ) 1) :
    0 ≤ entropyCorrection e f := by
  have hj := hc.2 (show (e,f) ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 from ⟨he,hf⟩)
    (show (f,e) ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 from ⟨hf,he⟩)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at hj
  rw [add_comm ((1/2:ℝ)*f) ((1/2)*e),entropyCorrection_self,entropyCorrection_comm f e] at hj
  linarith

theorem pureGap_equal_mean_nonneg_of_convex
    (hc : ConvexOn ℝ (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1)
      (fun p : ℝ × ℝ => entropyCorrection p.1 p.2))
    {m e f : ℝ} (hm : 0 < m) (hm' : m < 1)
    (he : e ∈ Ioc 0 (H m)) (hf : f ∈ Ioc 0 (H m)) :
    0 ≤ pureGap m m e f := by
  have hg := entropyCorrection_nonneg_of_convex hc
    ⟨he.1,he.2.trans (H_le_one m)⟩ ⟨hf.1,hf.2.trans (H_le_one m)⟩
  have hj := (phi_entropy_convexOn hm hm').2 he hf
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show (1/2:ℝ)*e+(1/2)*f=(e+f)/2 by ring] at hj
  simp only [pureGap,fourMomentLowerBound,candidateGap,sub_self,abs_zero,F,↓reduceIte,zero_add]
  rw [show (m+m)/2=m by ring]
  linarith

end GeneralCK


