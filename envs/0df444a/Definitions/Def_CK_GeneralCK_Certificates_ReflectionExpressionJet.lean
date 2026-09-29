-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionExpressionJet
-- name    : CK_GeneralCK_Certificates_ReflectionExpressionJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:06:56.533521+00:00
-- url     : https://prove2.me/theorems/bb1b749c-a602-4712-93c5-2a5e05298d12
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionExpressionJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionExpressionJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionExpressionJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionExpressionJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionExpressionJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionContactJet
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Certificates.ReflectionExpression
open Set
open GeneralCK.Certificates.Reflection
noncomputable section







@[simp] theorem sub_value (j k : Jet2) (t : ℝ) :
    (sub j k).value t = j.value t-k.value t := rfl
@[simp] theorem div_value (j k : Jet2) (t : ℝ) :
    (div j k).value t = j.value t/k.value t := by simp [div,Jet2.mul,Jet2.inv,div_eq_mul_inv]
@[simp] theorem pow_value (j : Jet2) (n : ℕ) (t : ℝ) :
    (pow j n).value t = (j.value t)^n := by
  induction n with
  | zero => simp [pow,Jet2.const]
  | succ n ih => simp [pow,Jet2.mul,ih,pow_succ,mul_comm]

theorem sub_sound {j k : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (hk : k.SoundOn s) :
    (sub j k).SoundOn s := hj.add hk.neg
theorem div_sound {j k : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (hk : k.SoundOn s)
    (hn : ∀ t ∈ s, k.value t ≠ 0) : (div j k).SoundOn s := hj.mul (hk.inv hn)
theorem pow_sound {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (n : ℕ) :
    (pow j n).SoundOn s := by
  induction n with
  | zero => exact Jet2.soundOn_const 1 s
  | succ n ih => exact hj.mul ih










@[simp] theorem entropy_value (j : Jet2) (t : ℝ) :
    (entropy j).value t = biasE (j.value t) := by
  simp [entropy,Jet2.const,Jet2.add,Jet2.mul,Jet2.log,biasE]
@[simp] theorem bfun_value (j : Jet2) (t : ℝ) :
    (bfun j).value t = biasB (j.value t) := by
  simp [bfun,Jet2.const,Jet2.log,biasB,pow_two]
@[simp] theorem atanh_value (j : Jet2) (t : ℝ) :
    (atanh j).value t = SmallMean.A (j.value t) := by
  simp [atanh,Jet2.const,Jet2.log,Jet2.add,SmallMean.A]

theorem entropy_sound {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hr : ∀ t ∈ s, -1 < j.value t ∧ j.value t < 1) : (entropy j).SoundOn s := by
  have hc := Jet2.soundOn_const 1 s
  have hp := hc.add hj
  have hm := sub_sound hc hj
  have hlp := hp.log (fun t ht => by dsimp [Jet2.add,Jet2.const]; linarith [(hr t ht).1])
  have hlm := hm.log (fun t ht => by simp only [sub_value,Jet2.const]; linarith [(hr t ht).2])
  exact sub_sound (Jet2.soundOn_const _ s)
    (div_sound ((hp.mul hlp).add (hm.mul hlm)) (Jet2.soundOn_const 2 s) (by intros; norm_num [Jet2.const]))

theorem bfun_sound {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hr : ∀ t ∈ s, -1 < j.value t ∧ j.value t < 1) : (bfun j).SoundOn s := by
  have hd := sub_sound (Jet2.soundOn_const 1 s) (pow_sound hj 2)
  have hl := hd.log (fun t ht => by simp only [sub_value,pow_value,Jet2.const]; nlinarith [(hr t ht).1,(hr t ht).2])
  exact sub_sound (Jet2.soundOn_const _ s)
    (div_sound hl (Jet2.soundOn_const 2 s) (by intros; norm_num [Jet2.const]))

theorem atanh_sound {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hr : ∀ t ∈ s, -1 < j.value t ∧ j.value t < 1) : (atanh j).SoundOn s := by
  have hden : ∀ t ∈ s, (sub (Jet2.const 1) j).value t ≠ 0 := by
    intro t ht; simp only [sub_value,Jet2.const]; linarith [(hr t ht).2]
  have hd := div_sound ((Jet2.soundOn_const 1 s).add hj)
    (sub_sound (Jet2.soundOn_const 1 s) hj) hden
  have hl := hd.log (fun t ht => by
    simp only [div_value,sub_value,Jet2.add,Jet2.const]
    exact div_ne_zero (by linarith [(hr t ht).1]) (by linarith [(hr t ht).2]))
  exact div_sound hl (Jet2.soundOn_const 2 s) (by intros; norm_num [Jet2.const])








@[simp] theorem secant_value (c a e : Jet2) (t : ℝ) :
    (secant c a e).value t = biasS (c.value t) (a.value t) (e.value t) := by
  simp [secant,Jet2.mul,Jet2.add,Jet2.const,biasS,SmallMean.A,pow_two]

theorem secant_sound {c a e : Jet2} {s : Set ℝ}
    (hc : c.SoundOn s) (ha : a.SoundOn s) (he : e.SoundOn s)
    (hcr : ∀ t ∈ s, 0 < c.value t ∧ c.value t < 1)
    (har : ∀ t ∈ s, 0 < a.value t ∧ a.value t < 1)
    (hep : ∀ t ∈ s, 0 < e.value t) : (secant c a e).SoundOn s := by
  have hcwide : ∀ t ∈ s, -1 < c.value t ∧ c.value t < 1 :=
    fun t ht => ⟨by linarith [(hcr t ht).1],(hcr t ht).2⟩
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
    GeneralCK.Reflection.biasB_pos (hcr t ht).1 (hcr t ht).2
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



























theorem normalized_value (a z : Jet2) (t : ℝ) :
    (normalized a z).value t = normalizedValue (a.value t) (z.value t) := by
  simp [normalized,normalizedValue,contactMinus,contactPlus,meanEntropy,radiusMinus,radiusPlus,
    Jet2.mul,Jet2.add,Jet2.const,Jet2.comp,reflectionContactJet]

private theorem biasE_pos {a : ℝ} (ha : 0 < a) (ha' : a < 1) : 0 < biasE a := by
  rw [biasE_eq_binEntropy (by linarith) ha']
  exact Real.binEntropy_pos (by linarith) (by linarith)

theorem normalized_soundOn {a z : Jet2} {s : Set ℝ}
    (ha : a.SoundOn s) (hz : z.SoundOn s)
    (har : ∀ t ∈ s, 0 < a.value t ∧ a.value t < 1)
    (hzr : ∀ t ∈ s, 0 < z.value t ∧ z.value t < 1) :
    (normalized a z).SoundOn s := by
  have hb := ha.mul hz
  have hbr : ∀ t ∈ s, 0 < (a.mul z).value t ∧ (a.mul z).value t < 1 := by
    intro t ht
    simp only [Jet2.mul]
    exact ⟨mul_pos (har t ht).1 (hzr t ht).1,
      (by nlinarith [(hzr t ht).2, mul_pos (sub_pos.mpr (har t ht).2) (hzr t ht).1])⟩
  have haE := entropy_sound ha (fun t ht => ⟨by linarith [(har t ht).1],(har t ht).2⟩)
  have hbE := entropy_sound hb (fun t ht => ⟨by linarith [(hbr t ht).1],(hbr t ht).2⟩)
  have he : (meanEntropy a z).SoundOn s :=
    div_sound (haE.add hbE) (Jet2.soundOn_const 2 s) (by intros; norm_num [Jet2.const])
  have hep : ∀ t ∈ s, 0 < (meanEntropy a z).value t := by
    intro t ht
    have hh1 := biasE_pos (har t ht).1 (har t ht).2
    have hh2 := biasE_pos (hbr t ht).1 (hbr t ht).2
    simp only [meanEntropy,div_value,Jet2.add,Jet2.const,entropy_value]
    positivity
  have hsm : (radiusMinus a z).SoundOn s :=
    div_sound (ha.mul (sub_sound (Jet2.soundOn_const 1 s) hz))
      (Jet2.soundOn_const 2 s) (by intros; norm_num [Jet2.const])
  have hsp : (radiusPlus a z).SoundOn s :=
    div_sound (ha.mul ((Jet2.soundOn_const 1 s).add hz))
      (Jet2.soundOn_const 2 s) (by intros; norm_num [Jet2.const])
  have hsmp : ∀ t ∈ s, 0 < (radiusMinus a z).value t := by
    intro t ht
    simp only [radiusMinus,div_value,Jet2.mul,sub_value,Jet2.const]
    exact div_pos (mul_pos (har t ht).1 (by linarith [(hzr t ht).2])) (by norm_num)
  have hspp : ∀ t ∈ s, 0 < (radiusPlus a z).value t := by
    intro t ht
    simp only [radiusPlus,div_value,Jet2.mul,Jet2.add,Jet2.const]
    exact div_pos (mul_pos (har t ht).1 (by linarith [(hzr t ht).1])) (by norm_num)
  have hym := div_sound he hsm (fun t ht => (hsmp t ht).ne')
  have hyp := div_sound he hsp (fun t ht => (hspp t ht).ne')
  have hymp : ∀ t ∈ s, 0 < (div (meanEntropy a z) (radiusMinus a z)).value t :=
    fun t ht => div_pos (hep t ht) (hsmp t ht)
  have hypp : ∀ t ∈ s, 0 < (div (meanEntropy a z) (radiusPlus a z)).value t :=
    fun t ht => div_pos (hep t ht) (hspp t ht)
  have hcm : (contactMinus a z).SoundOn s := reflectionContactJet_comp_soundOn hym hymp
  have hcp : (contactPlus a z).SoundOn s := reflectionContactJet_comp_soundOn hyp hypp
  have hcmr : ∀ t ∈ s, 0 < (contactMinus a z).value t ∧ (contactMinus a z).value t < 1 :=
    fun t ht => GeneralCK.Reflection.biasContact_mem (hymp t ht)
  have hcpr : ∀ t ∈ s, 0 < (contactPlus a z).value t ∧ (contactPlus a z).value t < 1 :=
    fun t ht => GeneralCK.Reflection.biasContact_mem (hypp t ht)
  have hS1 := secant_sound hcm ha he hcmr har hep
  have hS2 := secant_sound hcp ha he hcpr har hep
  have hden := pow_sound (sub_sound (Jet2.soundOn_const 1 s) (pow_sound ha 2)) 2
  have hbase := div_sound (((Jet2.soundOn_const 2 s).mul ha).mul hb) hden (fun t ht => by
    simp only [pow_value,sub_value,Jet2.const]
    apply pow_ne_zero
    nlinarith [(har t ht).1,(har t ht).2])
  exact div_sound (sub_sound (hbase.add hS1) hS2) ((pow_sound ha 3).mul hb) (fun t ht => by
    simp only [Jet2.mul,pow_value]
    exact mul_ne_zero (pow_ne_zero 3 (har t ht).1.ne')
      (mul_ne_zero (har t ht).1.ne' (hzr t ht).1.ne'))

end
end GeneralCK.Certificates.ReflectionExpression


