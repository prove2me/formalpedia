-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionRegularDifference_v2
-- name    : CK_GeneralCK_ReflectionRegularDifference_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T06:08:51.267402+00:00
-- url     : https://prove2.me/theorems/54b577d2-1205-4e57-925c-3d0b12947f23
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionRegularDifference` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionRegularDifference` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionRegularDifference` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionRegularDifference (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionRegularDifference.lean)

import Definitions.Def_CK_GeneralCK_ReflectionRegularContact
import Definitions.Def_CK_GeneralCK_ReflectionNormalized

-- ===== source module GeneralCK.ReflectionRegularDifference =====
section

namespace GeneralCK.Reflection.RegularDifference
open Certificates.Reflection

/-- Signed natural-unit perspective; the radius variable is extended evenly. -/
noncomputable def FNat (s e : ℝ) : ℝ :=
  2*s*SmallMean.A (regularContact (s/e))

noncomputable def entropy (a b : ℝ) : ℝ := (biasE a+biasE b)/2

/-- Regular signed reflection difference. No analyticity is asserted here. -/
noncomputable def Dreg (a b : ℝ) : ℝ :=
  a*SmallMean.A b+b*SmallMean.A a
    -FNat ((a+b)/2) (entropy a b)+FNat ((a-b)/2) (entropy a b)

theorem A_neg (x : ℝ) : SmallMean.A (-x) = -SmallMean.A x := by
  unfold SmallMean.A
  rw [show (1+-x)/(1- -x)=((1+x)/(1-x))⁻¹ by simp [sub_eq_add_neg],
    Real.log_inv]
  ring

theorem contact_neg (τ : ℝ) : regularContact (-τ) = -regularContact τ := by
  rcases lt_trichotomy τ 0 with h | h | h
  · rw [regularContact_pos_eq (by linarith), regularContact_neg_eq h]
    simp
  · subst τ; simp
  · rw [regularContact_neg_eq (by linarith), regularContact_pos_eq h]
    simp

@[simp] theorem FNat_zero (e : ℝ) : FNat 0 e = 0 := by simp [FNat]

theorem FNat_neg (s e : ℝ) : FNat (-s) e = FNat s e := by
  simp only [FNat, neg_div, contact_neg, A_neg]
  ring

theorem FNat_eq_F {s h : ℝ} (hs : 0 ≤ s) (hh : 0 < h) :
    FNat s (Real.log 2*h) = Real.log 2*F s h := by
  rcases hs.eq_or_lt with hs | hs
  · subst s; simp [FNat, F]
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  rw [FNat, regularContact_pos_eq (div_pos hs (mul_pos hl hh))]
  rw [show (s/(Real.log 2*h))⁻¹=Real.log 2*h/s by simp,
    biasContact_scaled_ratio hs.ne', SmallMean.A_eq_J]
  rw [show (1-(1-2*radialContact s h))/2=radialContact s h by ring]
  simp only [F, if_neg hs.ne']
  ring

theorem entropy_eq_bits {a b : ℝ} (ha : -1<a) (ha' : a<1)
    (hb : -1<b) (hb' : b<1) : entropy a b=Real.log 2*meanEntropy a b := by
  unfold entropy meanEntropy
  rw [biasE_eq_log_mul_E ha ha', biasE_eq_log_mul_E hb hb']
  ring

theorem Dreg_eq_D {a b : ℝ} (hb : 0≤b) (hba : b≤a) (ha : a<1) :
    Dreg a b=D a b := by
  have ha0 : -1<a := by linarith
  have hb0 : -1<b := by linarith
  have hb1 : b<1 := hba.trans_lt ha
  have he := meanEntropy_pos ha0 ha hb0 hb1
  unfold Dreg D
  rw [entropy_eq_bits ha0 ha hb0 hb1,
    FNat_eq_F (by linarith) he, FNat_eq_F (by linarith) he]

theorem Dreg_swap (a b : ℝ) : Dreg b a=Dreg a b := by
  have he : entropy b a=entropy a b := by unfold entropy; ring
  unfold Dreg
  rw [he, add_comm b a, show (b-a)/2= -((a-b)/2) by ring, FNat_neg]
  ring

theorem Dreg_neg_left (a b : ℝ) : Dreg (-a) b= -Dreg a b := by
  have he : entropy (-a) b=entropy a b := by simp [entropy, biasE_neg]
  unfold Dreg
  rw [he, A_neg, show (-a+b)/2= -((a-b)/2) by ring,
    show (-a-b)/2= -((a+b)/2) by ring, FNat_neg, FNat_neg]
  ring

theorem Dreg_neg_right (a b : ℝ) : Dreg a (-b)= -Dreg a b := by
  rw [Dreg_swap, Dreg_neg_left, Dreg_swap b a]

@[simp] theorem Dreg_zero (a : ℝ) : Dreg a 0=0 := by
  simp [Dreg, SmallMean.A]

theorem Dreg_diagonal {a : ℝ} (ha : -1<a) (ha' : a<1) : Dreg a a=0 := by
  by_cases h : 0≤a
  · rw [Dreg_eq_D h le_rfl ha', D_diagonal h ha']
  · have hn : 0≤ -a := by linarith
    have hn' : -a<1 := by linarith
    have hd : Dreg (-a) (-a)=0 := by
      rw [Dreg_eq_D hn le_rfl hn', D_diagonal hn hn']
    simpa only [Dreg_neg_left, Dreg_neg_right, neg_neg] using hd

end GeneralCK.Reflection.RegularDifference

end


