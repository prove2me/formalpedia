-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SignedReflectionJet
-- name    : CK_GeneralCK_Certificates_SignedReflectionJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:22.11055+00:00
-- url     : https://prove2.me/theorems/59660ea0-c26d-48f9-a25d-91af0e9d3cf2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SignedReflectionJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SignedReflectionJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SignedReflectionJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SignedReflectionJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SignedReflectionJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionExpressionJet

-- ===== source module GeneralCK.Certificates.SignedReflectionJet =====
section

namespace GeneralCK.Certificates.ReflectionExpression
open Set GeneralCK.Certificates.Reflection
noncomputable section

/-- The denominator stays positive on the entire signed bias domain, including zero. -/
theorem biasB_pos_signed {c : ℝ} (hc : -1 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith [sq_nonneg c])
  unfold biasB
  linarith [GeneralCK.log_two_pos]

theorem secant_sound_signed {c a e : Jet2} {s : Set ℝ}
    (hc : c.SoundOn s) (ha : a.SoundOn s) (he : e.SoundOn s)
    (hcr : ∀ t ∈ s, -1 < c.value t ∧ c.value t < 1)
    (har : ∀ t ∈ s, 0 < a.value t ∧ a.value t < 1)
    (hep : ∀ t ∈ s, 0 < e.value t) : (secant c a e).SoundOn s := by
  have hcwide : ∀ t ∈ s, -1 < c.value t ∧ c.value t < 1 :=
    hcr
  have hawide : ∀ t ∈ s, -1 < a.value t ∧ a.value t < 1 :=
    fun t ht => ⟨by linarith [(har t ht).1],(har t ht).2⟩
  have hc2 := pow_sound hc 2
  have hca := sub_sound (Jet2.soundOn_const 1 s) hc2
  have haa := sub_sound (Jet2.soundOn_const 1 s) (pow_sound ha 2)
  have hb := bfun_sound hc hcwide
  have hh := entropy_sound hc hcwide
  have hn := (hh.mul (sub_sound ((Jet2.soundOn_const 2 s).mul hb) hc2)).mul
    (pow_sound (hh.add (hc.mul (atanh_sound ha hawide))) 2)
  have hd := (((Jet2.soundOn_const 2 s).mul he).mul (pow_sound hca 2)).mul (pow_sound hb 3)
  have hp (t : ℝ) (ht : t ∈ s) : 0 < biasB (c.value t) :=
    biasB_pos_signed (hcr t ht).1 (hcr t ht).2
  have hcp (t : ℝ) (ht : t ∈ s) : 0 < 1-(c.value t)^2 := by nlinarith [(hcr t ht).1,(hcr t ht).2]
  have hap (t : ℝ) (ht : t ∈ s) : 0 < 1-(a.value t)^2 := by nlinarith [(har t ht).1,(har t ht).2]
  exact (div_sound hn hd (fun t ht => by
    have := hp t ht; have := hcp t ht; have := hep t ht
    simp only [Jet2.mul,Jet2.const,pow_value,sub_value,bfun_value]
    exact ne_of_gt (by positivity))).add
    (div_sound hc2 ((haa.mul hca).mul hb) (fun t ht => by
      have := hp t ht; have := hcp t ht; have := hap t ht
      simp only [Jet2.mul,Jet2.const,pow_value,sub_value,bfun_value]
      exact ne_of_gt (by positivity)))

/-- The signed secant formula has its finite analytic value at zero contact. -/
@[simp] theorem biasS_zero (a e : ℝ) : biasS 0 a e = Real.log 2/e := by
  have hL := GeneralCK.log_two_pos.ne'
  simp only [biasS,biasE,biasB,zero_mul,mul_zero,add_zero,sub_zero,Real.log_one,
    zero_div,one_pow]
  by_cases he : e=0
  · simp [he]
  · field_simp

@[simp] theorem secant_value_zero {c a e : Jet2} {t : ℝ} (hc : c.value t=0) :
    (secant c a e).value t = Real.log 2/e.value t := by
  rw [secant_value,hc,biasS_zero]

end
end GeneralCK.Certificates.ReflectionExpression

end


