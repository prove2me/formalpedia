-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasCore
-- name    : CK_GeneralCK_ReflectionHighBiasCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:58:17.669001+00:00
-- url     : https://prove2.me/theorems/936505be-dbca-45b5-aa94-30975295cfee
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasCore.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioFormula
import Definitions.Def_CK_GeneralCK_ReflectionRegularContact
import Definitions.Def_CK_GeneralCK_ReflectionHighBiasLog

-- ===== source module GeneralCK.ReflectionHighBiasCore =====
section

namespace GeneralCK.Reflection.HighBias
open Set Certificates.Reflection SmallRatio

noncomputable section

def Cs (c e : ℝ) : ℝ := (biasE c)^2/(e*biasB c)
def C2 (c e : ℝ) : ℝ := Cs c e*(Kprime c e*c^2+2*K c e*c)
def C1 (c e : ℝ) : ℝ :=
  Cs c e*(2*Kprime c e*c*biasE c+2*K c e*(biasE c-c*SmallMean.A c))
def C0 (c e : ℝ) : ℝ :=
  Cs c e*(Kprime c e*(biasE c)^2-2*K c e*biasE c*SmallMean.A c)
def Cq (c e : ℝ) : ℝ := Cs c e*Mprime c

theorem P_eq_coefficients {a e s : ℝ} (ha : 0<a) (ha' : a<1) (he : 0<e) (hs : 0<s) :
    P a e s =
      C2 (biasContact (e/s)) e*(SmallMean.A a)^2+
      C1 (biasContact (e/s)) e*SmallMean.A a+C0 (biasContact (e/s)) e+
      Cq (biasContact (e/s)) e/(1-a^2) := by
  rw [P_eq_formula ha ha' he hs]
  dsimp only [PFormula]
  rw [ScFormula_polynomial]
  unfold C2 C1 C0 Cq Cs
  ring

theorem derivative_le_of_coefficients {a e s : ℝ}
    (ha : 0<a) (ha' : a<1) (he : 0<e) (hs : 0<s)
    (h2 : C2 (biasContact (e/s)) e≤6000)
    (h1 : C1 (biasContact (e/s)) e≤8000)
    (h0 : C0 (biasContact (e/s)) e≤3000)
    (hq : Cq (biasContact (e/s)) e≤210) :
    P a e s≤6000*(SmallMean.A a)^2+8000*SmallMean.A a+3000+210/(1-a^2) := by
  rw [P_eq_coefficients ha ha' he hs]
  have hA : 0≤SmallMean.A a := ha.le.trans (SmallMean.A_lower ha.le ha')
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    (mul_le_mul_of_nonneg_right h1 hA)) h0)
    (div_le_div_of_nonneg_right hq (by nlinarith))

theorem mean_entropy_bounds {a b : ℝ}
    (ha : a ∈ Ico (999/1000:ℝ) 1) (hb : b ∈ Icc (0:ℝ) (1/2))
    (hEa : biasE (999/1000)≤1/200) (hEb : 14/25≤biasE (1/2))
    (hL : Real.log 2≤139/200) :
    Bounds (7/25) (7/20) ((biasE a+biasE b)/2) := by
  have ha0 : 0<a := by linarith [ha.1]
  have h1 := bounds_biasE (show Bounds (999/1000) 1 a from ⟨ha.1,ha.2.le⟩)
    (by norm_num) le_rfl (by norm_num [biasE] : (0:ℝ)≤biasE 1) hEa
  have h2 := bounds_biasE (show Bounds 0 (1/2) b from hb)
    le_rfl (by norm_num) hEb (show biasE 0≤139/200 by simpa [biasE] using hL)
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

theorem radius_bounds {a b s : ℝ}
    (ha : a ∈ Ico (999/1000:ℝ) 1) (hb : b ∈ Icc (0:ℝ) (1/2))
    (hs : s ∈ Icc ((a-b)/2) ((a+b)/2)) : Bounds (499/2000) (3/4) s := by
  constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hs.1,hs.2]

theorem contact_bounds {e s : ℝ} (he : Bounds (7/25) (7/20) e)
    (hs : Bounds (499/2000) (3/4) s)
    (hl : (7/20)*(2/5)≤(499/2000)*biasE (2/5))
    (hu : (3/4)*biasE (9/10)≤(7/25)*(9/10)) :
    Bounds (2/5) (9/10) (biasContact (e/s)) := by
  have he0 : 0<e := by linarith [he.1]
  have hs0 : 0<s := by linarith [hs.1]
  have hy := div_pos he0 hs0
  have hc := biasContact_mem hy
  have heq := (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hEl : 0≤biasE (2/5) := (biasE_pos_wide (by norm_num) (by norm_num)).le
  have hEu : 0≤biasE (9/10) := (biasE_pos_wide (by norm_num) (by norm_num)).le
  apply contact_bracket hc.1.le hc.2.le (by norm_num) (by norm_num) (by norm_num) hy heq
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hs0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) hEl,he.2]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hs0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hEu,he.1]

/-- All numerical obligations for this unbounded high-bias region are isolated
as five fixed scalar comparisons and one compact coefficient box. -/
theorem curvature_pos_of_certificates
    (hEa : biasE (999/1000)≤1/200) (hEb : 14/25≤biasE (1/2))
    (hL : Real.log 2≤139/200)
    (hl : (7/20)*(2/5)≤(499/2000)*biasE (2/5))
    (hu : (3/4)*biasE (9/10)≤(7/25)*(9/10))
    (hC : ∀ c e : ℝ, Bounds (2/5) (9/10) c → Bounds (7/25) (7/20) e →
      C2 c e≤6000 ∧ C1 c e≤8000 ∧ C0 c e≤3000 ∧ Cq c e≤210)
    {a z : ℝ} (ha : a ∈ Ico (999/1000:ℝ) 1) (hz : 0<z) (hb : a*z≤1/2) :
    0<curvature a (a*z) := by
  have ha0 : 0<a := by linarith [ha.1]
  have hab : 0<a*z := mul_pos ha0 hz
  have hba : a*z<a := by linarith [ha.1]
  have hz1 : z<1 := by nlinarith
  have he := mean_entropy_bounds ha ⟨hab.le,hb⟩ hEa hEb hL
  have he0 : 0<(biasE a+biasE (a*z))/2 := by linarith [he.1]
  apply curvature_pos_of_derivative_bound ha0 ha.2 hz hz1
  · intro s hs
    have hr := radius_bounds ha (show a*z ∈ Icc (0:ℝ) (1/2) from ⟨hab.le,hb⟩)
      (s := s) (by
        constructor <;> nlinarith [hs.1,hs.2])
    have hs0 : 0<s := by linarith [hr.1]
    have hc := contact_bounds he hr hl hu
    have hcoeff := hC _ _ hc he
    exact derivative_le_of_coefficients ha0 ha.2 he0 hs0
      hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 hcoeff.2.2.2
  · exact HighBiasLog.coefficient_domination ha.1 ha.2

end
end GeneralCK.Reflection.HighBias

end


