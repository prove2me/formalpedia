-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionBounds
-- name    : CK_GeneralCK_Certificates_ReflectionBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:22:59.788492+00:00
-- url     : https://prove2.me/theorems/907a8d3c-f364-43f8-a823-b9cab2de2ebf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds
import Definitions.Def_CK_GeneralCK_RadialContact
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates.Reflection



theorem bounds_const (x : ℝ) : Bounds x x x := ⟨le_rfl, le_rfl⟩

theorem bounds_widen {a b l u x : ℝ} (hx : Bounds a b x)
    (hl : l ≤ a) (hu : b ≤ u) : Bounds l u x := ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem bounds_add {a b c d l u x y : ℝ} (hx : Bounds a b x)
    (hy : Bounds c d y) (hl : l ≤ a+c) (hu : b+d ≤ u) : Bounds l u (x+y) := by
  constructor <;> dsimp [Bounds] at * <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem bounds_neg {a b x : ℝ} (hx : Bounds a b x) : Bounds (-b) (-a) (-x) := by
  constructor <;> linarith [hx.1,hx.2]

private theorem bilinear_upper {a b c d x y u : ℝ} (hx : Bounds a b x)
    (hy : Bounds c d y) (h1 : a*c ≤ u) (h2 : a*d ≤ u)
    (h3 : b*c ≤ u) (h4 : b*d ≤ u) : x*y ≤ u := by
  have hc : x*c ≤ u := by
    rcases le_total 0 c with hc | hc
    · exact (mul_le_mul_of_nonneg_right hx.2 hc).trans h3
    · exact (mul_le_mul_of_nonpos_right hx.1 hc).trans h1
  have hd : x*d ≤ u := by
    rcases le_total 0 d with hd | hd
    · exact (mul_le_mul_of_nonneg_right hx.2 hd).trans h4
    · exact (mul_le_mul_of_nonpos_right hx.1 hd).trans h2
  rcases le_total 0 x with h | h
  · exact (mul_le_mul_of_nonneg_left hy.2 h).trans hd
  · exact (mul_le_mul_of_nonpos_left hy.1 h).trans hc

theorem bounds_mul {a b c d l u x y : ℝ} (hx : Bounds a b x)
    (hy : Bounds c d y) (hl1 : l ≤ a*c) (hl2 : l ≤ a*d)
    (hl3 : l ≤ b*c) (hl4 : l ≤ b*d) (hu1 : a*c ≤ u)
    (hu2 : a*d ≤ u) (hu3 : b*c ≤ u) (hu4 : b*d ≤ u) : Bounds l u (x*y) := by
  refine ⟨?_,bilinear_upper hx hy hu1 hu2 hu3 hu4⟩
  have h := bilinear_upper hx (bounds_neg hy)
    (show a * -d ≤ -l by nlinarith) (show a * -c ≤ -l by nlinarith)
    (show b * -d ≤ -l by nlinarith) (show b * -c ≤ -l by nlinarith)
  nlinarith

theorem bounds_inv {a b l u x : ℝ} (hx : Bounds a b x) (ha : 0 < a)
    (hl : l ≤ 1/b) (hu : 1/a ≤ u) : Bounds l u (x⁻¹) := by
  have hxp : 0 < x := ha.trans_le hx.1
  constructor
  · exact hl.trans (by simpa only [one_div] using inv_anti₀ hxp hx.2)
  · have hi : x⁻¹ ≤ 1/a := by simpa only [one_div] using inv_anti₀ ha hx.1
    exact hi.trans hu

theorem bounds_log {a b l u x : ℝ} (hx : Bounds a b x) (ha : 0 < a)
    (hl : l ≤ Real.log a) (hu : Real.log b ≤ u) : Bounds l u (Real.log x) :=
  ⟨hl.trans (Real.log_le_log ha hx.1), (Real.log_le_log (ha.trans_le hx.1) hx.2).trans hu⟩










theorem biasE_eq_binEntropy {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.binEntropy ((1-c)/2) := by
  have hm : 0 < 1-c := by linarith
  have hp : 0 < 1+c := by linarith
  rw [Real.binEntropy]
  rw [Real.log_inv, Real.log_inv]
  rw [show 1-(1-c)/2 = (1+c)/2 by ring]
  rw [Real.log_div hm.ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_div hp.ne' (by norm_num : (2:ℝ) ≠ 0)]
  unfold biasE
  ring

theorem biasE_antitone : AntitoneOn biasE (Set.Icc 0 1) := by
  intro a ha b hb hab
  by_cases ha1 : a = 1
  · have he : b=a := by linarith [hb.2]
    rw [he]
  by_cases hb1 : b = 1
  · subst b
    have hnon := Real.binEntropy_nonneg (show 0 ≤ (1-a)/2 by linarith)
      (show (1-a)/2 ≤ 1 by linarith [ha.1])
    rw [biasE_eq_binEntropy (by linarith [ha.1]) (lt_of_le_of_ne ha.2 ha1)]
    norm_num [biasE]
    exact hnon
  rw [biasE_eq_binEntropy (by linarith [hb.1]) (lt_of_le_of_ne hb.2 hb1),
    biasE_eq_binEntropy (by linarith [ha.1]) (lt_of_le_of_ne ha.2 ha1)]
  exact Real.binEntropy_strictMonoOn.monotoneOn
    ⟨by linarith [hb.2],by linarith [hb.1]⟩
    ⟨by linarith [ha.2],by linarith [ha.1]⟩ (by linarith)

theorem bounds_biasE {a b l u x : ℝ} (hx : Bounds a b x) (ha : 0 ≤ a)
    (hb : b ≤ 1) (hl : l ≤ biasE b) (hu : biasE a ≤ u) : Bounds l u (biasE x) := by
  have hxx : x ∈ Set.Icc 0 1 := ⟨ha.trans hx.1,hx.2.trans hb⟩
  exact ⟨hl.trans (biasE_antitone hxx ⟨ha.trans (hx.1.trans hx.2),hb⟩ hx.2),
    (biasE_antitone ⟨ha,(hx.1.trans hx.2).trans hb⟩ hxx hx.1).trans hu⟩

theorem contact_bracket {c y l u : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hl : 0 ≤ l) (hu : u ≤ 1) (hlu : l ≤ u) (hy : 0 < y)
    (heq : biasE c = y*c) (hlo : y*l ≤ biasE l) (hhi : biasE u ≤ y*u) :
    Bounds l u c := by
  constructor
  · by_contra hn
    have hh : c < l := lt_of_not_ge hn
    have hm := biasE_antitone ⟨hc,hc'⟩ ⟨hl,hlu.trans hu⟩ hh.le
    have ht := mul_lt_mul_of_pos_left hh hy
    linarith
  · by_contra hn
    have hh : u < c := lt_of_not_ge hn
    have hm := biasE_antitone ⟨hl.trans hlu,hu⟩ ⟨hc,hc'⟩ hh.le
    have ht := mul_lt_mul_of_pos_left hh hy
    linarith

end GeneralCK.Certificates.Reflection


