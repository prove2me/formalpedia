-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_RegularReflectionExpressionJet
-- name    : CK_GeneralCK_Certificates_RegularReflectionExpressionJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:04:33.197453+00:00
-- url     : https://prove2.me/theorems/d7b4a269-735e-40b3-8af7-587e05e4475d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.RegularReflectionExpressionJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.RegularReflectionExpressionJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.RegularReflectionExpressionJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.RegularReflectionExpressionJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/RegularReflectionExpressionJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SignedReflectionJet
import Definitions.Def_CK_GeneralCK_Certificates_RegularContactJet

-- ===== source module GeneralCK.Certificates.RegularReflectionExpressionJet =====
section

namespace GeneralCK.Certificates.RegularReflectionExpression
open Set GeneralCK.Certificates.Reflection
open GeneralCK.Certificates.ReflectionExpression
noncomputable section

def contactMinus (a z : Jet2) : Jet2 :=
  regularContactJet.comp (div (radiusMinus a z) (meanEntropy a z))
def contactPlus (a z : Jet2) : Jet2 :=
  regularContactJet.comp (div (radiusPlus a z) (meanEntropy a z))

/-- A compositional jet for the normalized natural-entropy reflection curvature. -/
def normalized (a z : Jet2) : Jet2 :=
  div (sub ((div (((Jet2.const 2).mul a).mul (a.mul z))
    (pow (sub (Jet2.const 1) (pow a 2)) 2)).add
    (secant (contactMinus a z) a (meanEntropy a z)))
    (secant (contactPlus a z) a (meanEntropy a z))) ((pow a 3).mul (a.mul z))

/-- The source expression with its actual implicit bias contacts. -/
def normalizedValue (a z : ℝ) : ℝ :=
  let b := a*z
  let e := (biasE a+biasE b)/2
  let cm := GeneralCK.Reflection.regularContact ((a*(1-z)/2)/e)
  let cp := GeneralCK.Reflection.regularContact ((a*(1+z)/2)/e)
  (2*a*b/(1-a^2)^2+biasS cm a e-biasS cp a e)/(a^3*b)

theorem normalized_value (a z : Jet2) (t : ℝ) :
    (normalized a z).value t = normalizedValue (a.value t) (z.value t) := by
  simp [normalized,normalizedValue,contactMinus,contactPlus,meanEntropy,radiusMinus,radiusPlus,
    Jet2.mul,Jet2.add,Jet2.const,Jet2.comp,regularContactJet]

private theorem biasE_pos {a : ℝ} (ha : 0 < a) (ha' : a < 1) : 0 < biasE a := by
  rw [biasE_eq_binEntropy (by linarith) ha']
  exact Real.binEntropy_pos (by linarith) (by linarith)

theorem normalized_soundOn {a z : Jet2} {s : Set ℝ}
    (ha : a.SoundOn s) (hz : z.SoundOn s)
    (har : ∀ t ∈ s, 0 < a.value t ∧ a.value t < 1)
    (hzr : ∀ t ∈ s, 0 < z.value t ∧ a.value t*z.value t < 1) :
    (normalized a z).SoundOn s := by
  have hb := ha.mul hz
  have hbr : ∀ t ∈ s, 0 < (a.mul z).value t ∧ (a.mul z).value t < 1 := by
    intro t ht
    simp only [Jet2.mul]
    exact ⟨mul_pos (har t ht).1 (hzr t ht).1,(hzr t ht).2⟩
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
  have hym := div_sound hsm he (fun t ht => (hep t ht).ne')
  have hyp := div_sound hsp he (fun t ht => (hep t ht).ne')
  have hcm : (contactMinus a z).SoundOn s :=
    (regularContactJet_soundOn Set.univ).comp hym (by intro t ht; trivial)
  have hcp : (contactPlus a z).SoundOn s :=
    (regularContactJet_soundOn Set.univ).comp hyp (by intro t ht; trivial)
  have hcmr : forall t, t ∈ s → -1 < (contactMinus a z).value t ∧ (contactMinus a z).value t < 1 :=
    fun t ht => GeneralCK.Reflection.regularContact_mem _
  have hcpr : forall t, t ∈ s → -1 < (contactPlus a z).value t ∧ (contactPlus a z).value t < 1 :=
    fun t ht => GeneralCK.Reflection.regularContact_mem _
  have hS1 := secant_sound_signed hcm ha he hcmr har hep
  have hS2 := secant_sound_signed hcp ha he hcpr har hep
  have hden := pow_sound (sub_sound (Jet2.soundOn_const 1 s) (pow_sound ha 2)) 2
  have hbase := div_sound (((Jet2.soundOn_const 2 s).mul ha).mul hb) hden (fun t ht => by
    simp only [pow_value,sub_value,Jet2.const]
    apply pow_ne_zero
    nlinarith [(har t ht).1,(har t ht).2])
  exact div_sound (sub_sound (hbase.add hS1) hS2) ((pow_sound ha 3).mul hb) (fun t ht => by
    simp only [Jet2.mul,pow_value]
    exact mul_ne_zero (pow_ne_zero 3 (har t ht).1.ne')
      (mul_ne_zero (har t ht).1.ne' (hzr t ht).1.ne'))

theorem normalizedValue_eq {a z : ℝ} (ha : 0<a) (ha' : a<1)
    (hz : 0<z) (hz' : z<1) : normalizedValue a z = ReflectionExpression.normalizedValue a z := by
  have hb : 0<a*z := mul_pos ha hz
  have hb' : a*z<1 := by nlinarith [mul_pos (sub_pos.mpr ha') hz]
  have he : 0<(biasE a+biasE (a*z))/2 := by
    have h1 := biasE_pos ha ha'
    have h2 := biasE_pos hb hb'
    positivity
  have hm : 0<a*(1-z)/2 := div_pos (mul_pos ha (sub_pos.mpr hz')) (by norm_num)
  have hp : 0<a*(1+z)/2 := div_pos (mul_pos ha (by linarith)) (by norm_num)
  simp only [normalizedValue,ReflectionExpression.normalizedValue]
  rw [GeneralCK.Reflection.regularContact_pos_eq (div_pos hm he),
    GeneralCK.Reflection.regularContact_pos_eq (div_pos hp he)]
  simp only [inv_div]

end
end GeneralCK.Certificates.RegularReflectionExpression

end


