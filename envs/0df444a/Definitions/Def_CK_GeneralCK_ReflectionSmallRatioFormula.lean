-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallRatioFormula
-- name    : CK_GeneralCK_ReflectionSmallRatioFormula
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:51:29.879602+00:00
-- url     : https://prove2.me/theorems/8b34dc6a-f53d-4e3c-92a4-852d2476d41e
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallRatioFormula` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallRatioFormula` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallRatioFormula` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallRatioFormula (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallRatioFormula.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallRatio

-- ===== source module GeneralCK.ReflectionSmallRatioFormula =====
section

namespace GeneralCK.Reflection.SmallRatio
open Certificates.Reflection
noncomputable section

/-- The K and M factors used by the source high-bias coefficient kernel. -/
def K (c e : ℝ) : ℝ :=
  biasE c*(2*biasB c-c^2)/(2*e*(1-c^2)^2*(biasB c)^3)
def M (c : ℝ) : ℝ := c^2/((1-c^2)*biasB c)

/-- Factored derivative with no reciprocal of E or of 2B-c². -/
def Kprime (c e : ℝ) : ℝ :=
  (-SmallMean.A c*(2*biasB c-c^2)+biasE c*(2*(c/(1-c^2))-2*c)) /
    (2*e*(1-c^2)^2*(biasB c)^3) +
  K c e*(4*c/(1-c^2)-3*c/((1-c^2)*biasB c))

def Mprime (c : ℝ) : ℝ := c*(2*biasB c-c^2)/((1-c^2)^2*(biasB c)^2)

theorem hasDerivAt_K {c e : ℝ} (hc : 0 < c) (hc' : c < 1) (he : 0 < e) :
    HasDerivAt (fun c => K c e) (Kprime c e) c := by
  have hd0 : 1-c^2 ≠ 0 := by nlinarith
  have hb0 := (biasB_pos hc hc').ne'
  have hh := hasDerivAt_biasE (by linarith) hc'
  have hb := hasDerivAt_biasB (by linarith) hc'
  have hi := hasDerivAt_id c
  have hd := (hi.pow 2).const_sub 1
  have hnum := hh.mul ((hb.const_mul 2).sub (hi.pow 2))
  have hden := (((hd.pow 2).const_mul (2*e)).mul (hb.pow 3))
  have hf := hnum.div hden (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) he.ne')
    (pow_ne_zero 2 hd0)) (pow_ne_zero 3 hb0))
  convert! hf using 1
  simp only [Kprime,K,id_eq,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply]
  field_simp [he.ne',hd0,hb0]
  ring

theorem hasDerivAt_M {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    HasDerivAt M (Mprime c) c := by
  have hd0 : 1-c^2 ≠ 0 := by nlinarith
  have hb0 := (biasB_pos hc hc').ne'
  have hi := hasDerivAt_id c
  have hd := ((hi.pow 2).const_sub 1).mul (hasDerivAt_biasB (by linarith) hc')
  have hf := (hi.pow 2).div hd (mul_ne_zero hd0 hb0)
  convert! hf using 1
  simp only [Mprime,id_eq,Pi.pow_apply,Pi.mul_apply]
  field_simp [hd0,hb0]
  ring

theorem biasS_factor (c a e : ℝ) :
    biasS c a e = K c e*(biasE c+c*SmallMean.A a)^2 + (1/(1-a^2))*M c := by
  simp only [biasS,K,M,SmallMean.A,pow_two,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Explicit first derivative of the source S expression, preserving its factors. -/
def ScFormula (c a e : ℝ) : ℝ :=
  Kprime c e*(biasE c+c*SmallMean.A a)^2 +
  2*K c e*(biasE c+c*SmallMean.A a)*(SmallMean.A a-SmallMean.A c) +
  (1/(1-a^2))*Mprime c

theorem hasDerivAt_S_formula {c a e : ℝ} (hc : 0 < c) (hc' : c < 1) (he : 0 < e) :
    HasDerivAt (fun c => biasS c a e) (ScFormula c a e) c := by
  have hh := (hasDerivAt_biasE (by linarith) hc').add
    ((hasDerivAt_id c).mul_const (SmallMean.A a))
  have hf := ((hasDerivAt_K hc hc' he).mul (hh.pow 2)).add
    ((hasDerivAt_M hc hc').const_mul (1/(1-a^2)))
  have hg := hf.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => biasS_factor t a e))
  convert! hg using 1
  simp only [ScFormula,id_eq,Pi.pow_apply,Pi.add_apply]
  ring

theorem Sc_eq_formula {c a e : ℝ} (hc : 0 < c) (hc' : c < 1)
    (ha : 0 < a) (ha' : a < 1) (he : 0 < e) : Sc c a e = ScFormula c a e :=
  (hasDerivAt_S ha ha' he hc hc').unique (hasDerivAt_S_formula hc hc' he)

def PFormula (a e s : ℝ) : ℝ :=
  let c := biasContact (e/s)
  ScFormula c a e*(biasE c)^2/(e*biasB c)

theorem P_eq_formula {a e s : ℝ} (ha : 0 < a) (ha' : a < 1) (he : 0 < e)
    (hs : 0 < s) : P a e s = PFormula a e s := by
  have hc := biasContact_mem (div_pos he hs)
  dsimp only [P,PFormula]
  rw [Sc_eq_formula hc.1 hc.2 ha ha' he]

/-- The source polynomial-in-atanh(a) coefficient arrangement. -/
theorem ScFormula_polynomial (c a e : ℝ) : ScFormula c a e =
    (Kprime c e*c^2+2*K c e*c)*(SmallMean.A a)^2 +
    (2*Kprime c e*c*biasE c+2*K c e*(biasE c-c*SmallMean.A c))*SmallMean.A a +
    (Kprime c e*(biasE c)^2-2*K c e*biasE c*SmallMean.A c) +
    (1/(1-a^2))*Mprime c := by
  unfold ScFormula
  ring

end
end GeneralCK.Reflection.SmallRatio

end


