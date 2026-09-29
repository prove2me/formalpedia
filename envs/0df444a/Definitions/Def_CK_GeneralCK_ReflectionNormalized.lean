-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionNormalized
-- name    : CK_GeneralCK_ReflectionNormalized
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:13:08.763683+00:00
-- url     : https://prove2.me/theorems/d3fed6e7-32dc-4bba-a7ad-a7a39dab8a1a
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionNormalized` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionNormalized` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionNormalized` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionNormalized (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionNormalized.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionExpressionJet

namespace GeneralCK.Reflection
open Certificates.Reflection Certificates.Mixed

private theorem normalized_biasE_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasE (1-2*v) = hn v := by
  rw [biasE_eq_log_mul_E (by linarith) (by linarith),hn_eq_H_mul_log]
  unfold E
  rw [show (1-(1-2*v))/2=v by ring]
  ring

private theorem normalized_biasB_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasB (1-2*v) = kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  unfold biasB kap
  rw [show 1-(1-2*v)*(1-2*v)=2^2*(v*(1-v)) by ring,
    Real.log_mul (by norm_num : (2:ℝ)^2 ≠ 0) hp.ne',Real.log_pow]
  ring

theorem normalized_biasS_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) (a e : ℝ) :
    biasS (1-2*v) a (Real.log 2*e) =
      reflectionS v e (SmallMean.A a) (1/(1-a^2)) := by
  unfold biasS
  rw [normalized_biasE_probability hv hv',normalized_biasB_probability hv hv']
  unfold reflectionS SmallMean.A
  rw [show 1-(1-2*v)*(1-2*v)=4*v*(1-v) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev,pow_two]
  ring

/-- The natural-ratio bias contact is the bias of the bit-entropy radial contact. -/
theorem biasContact_scaled_ratio {s : ℝ} (hs : s ≠ 0) (e : ℝ) :
    biasContact (Real.log 2*e/s) = 1-2*radialContact s e := by
  unfold biasContact
  rw [radialContact_normalize_radius hs e]
  congr 2
  field_simp

/-- Exact normalization and entropy-unit conversion, independent of certificates. -/
theorem normalizedValue_eq_curvature {a z : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hz : 0 < z) (hz' : z < 1) :
    Certificates.ReflectionExpression.normalizedValue a z = curvature a (a*z)/(a^4*z) := by
  have hb : 0 < a*z := mul_pos ha hz
  have hba : a*z < a := by nlinarith
  have hb' : a*z < 1 := hba.trans ha'
  have he : 0 < meanEntropy a (a*z) :=
    meanEntropy_pos (by linarith) ha' (by linarith) hb'
  have hm : 0 < (a-a*z)/2 := by linarith
  have hp : 0 < (a+a*z)/2 := by linarith
  have hE : (biasE a+biasE (a*z))/2 = Real.log 2*meanEntropy a (a*z) := by
    rw [biasE_eq_log_mul_E (by linarith) ha',biasE_eq_log_mul_E (by linarith) hb']
    unfold meanEntropy
    ring
  have hvm := radialContact_pos hm he
  have hvm' : radialContact ((a-a*z)/2) (meanEntropy a (a*z)) < 1 :=
    (radialContact_lt_half hm he).trans (by norm_num)
  have hvp := radialContact_pos hp he
  have hvp' : radialContact ((a+a*z)/2) (meanEntropy a (a*z)) < 1 :=
    (radialContact_lt_half hp he).trans (by norm_num)
  unfold Certificates.ReflectionExpression.normalizedValue
  dsimp only
  rw [hE,show a*(1-z)/2=(a-a*z)/2 by ring,show a*(1+z)/2=(a+a*z)/2 by ring,
    biasContact_scaled_ratio hm.ne',biasContact_scaled_ratio hp.ne',
    normalized_biasS_probability hvm hvm',normalized_biasS_probability hvp hvp']
  unfold curvature
  rw [show a^3*(a*z)=a^4*z by ring]
  congr 1
  ring

theorem curvature_pos_of_normalizedValue_pos {a z : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hz : 0 < z) (hz' : z < 1)
    (hpos : 0 < Certificates.ReflectionExpression.normalizedValue a z) :
    0 < curvature a (a*z) := by
  rw [normalizedValue_eq_curvature ha ha' hz hz'] at hpos
  exact (div_pos_iff_of_pos_right (mul_pos (pow_pos ha 4) hz)).mp hpos

end GeneralCK.Reflection


