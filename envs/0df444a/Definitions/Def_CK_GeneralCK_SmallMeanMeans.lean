-- Prove2me | Definitions.Def_CK_GeneralCK_SmallMeanMeans
-- name    : CK_GeneralCK_SmallMeanMeans
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:34:18.788229+00:00
-- url     : https://prove2.me/theorems/cf5428ed-eeca-4aee-bb89-cccf4422c781
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallMeanMeans` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallMeanMeans` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallMeanMeans` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallMeanMeans (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallMeanMeans.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanEstimates
import Definitions.Def_CK_GeneralCK_DeterministicCap

namespace GeneralCK.SmallMean

theorem normalized_entropy_chain {m r k : ℝ} (hm : 0 < m) (hm' : m < 1)
    (hr : 0 ≤ r) (hr' : r < 1) (hb : m*(1+r) < 1) (hk : k = m/(1-m)) :
    Real.log 2 * (H m-(H (m*(1-r))+H (m*(1+r)))/2) =
      m*Cn r+(1-m)*Cn (k*r) := by
  have ha0 : 0 < m*(1-r) := by positivity
  have hb0 : 0 < m*(1+r) := by positivity
  have ha1 : m*(1-r) < 1 := by nlinarith
  have he := deterministic_entropy_chain ha0 ha1 hb0 hb
  have hsum : m*(1-r)+m*(1+r)=2*m := by ring
  have hp : m*(1-r)/(m*(1-r)+m*(1+r))=(1-r)/2 := by field_simp; ring
  have hq : (1-m*(1+r))/(2-m*(1-r)-m*(1+r))=(1-k*r)/2 := by
    have ht : 2-m*(1-r)-m*(1+r) ≠ 0 := by nlinarith
    apply (div_eq_iff ht).mpr
    rw [hk]
    field_simp [show 1-m ≠ 0 by linarith]
    ring
  rw [hp, hq, hsum] at he
  have hmdiv : 2*m/2=m := by ring
  rw [hmdiv] at he
  rw [he]
  unfold Cn
  ring

theorem normalized_cost_chain {m r k : ℝ} (hm : 0 < m) (hm' : m < 1)
    (hr : 0 ≤ r) (hr' : r < 1) (hb : m*(1+r) < 1) (hk : k = m/(1-m)) :
    Real.log 2 * interiorCost (m*(1-r)) (m*(1+r)) =
      2*m*r*A r+2*(1-m)*(k*r)*A (k*r) := by
  have hmc : 1-m ≠ 0 := by linarith
  have hma : 1-m*(1-r) ≠ 0 := by nlinarith
  have hmb : 1-m*(1+r) ≠ 0 := by linarith
  have hmr : m*(1-r) ≠ 0 := by positivity
  have hpr : m*(1+r) ≠ 0 := by positivity
  have hk' : (1+k*r)/(1-k*r)=(1-m*(1-r))/(1-m*(1+r)) := by
    rw [hk]
    have ht : 1-m/(1-m)*r = (1-m*(1+r))/(1-m) := by field_simp [hmc]; ring
    rw [ht]
    field_simp [hmc, hmb]
    ring
  unfold interiorCost J A
  rw [hk']
  rw [Real.log_div hma hmr, Real.log_div hmb hpr,
    Real.log_div (by positivity : 1+r ≠ 0) (by linarith : 1-r ≠ 0),
    Real.log_div hma hmb,
    Real.log_mul hm.ne' (by linarith : 1-r ≠ 0),
    Real.log_mul hm.ne' (by positivity : 1+r ≠ 0)]
  rw [hk]
  field_simp [log_two_pos.ne', hmc]
  ring

theorem normalized_estimates {m r k delta j : ℝ}
    (hm : 0 < m) (hm' : m < 1) (hr : 0 < r) (hr' : r < 1)
    (hk : k = m/(1-m)) (hkmax : k ≤ 1/31)
    (hdelta : Real.log 2*delta = m*Cn r+(1-m)*Cn (k*r))
    (hj : Real.log 2*j = 2*m*r*A r+2*(1-m)*(k*r)*A (k*r)) :
    0 < delta ∧ delta ≤ r^2/31 ∧ (4+(1862/2883)*r^2)*delta ≤ j ∧
      gamma r*delta ≤ 2*k*r^2/((1+r)*(1+k*r)) := by
  have hmc : 0 < 1-m := by linarith
  have hk0 : 0 < k := by rw [hk]; positivity
  have hk1 : k ≤ 1 := by linarith
  have hkr : 0 < k*r := mul_pos hk0 hr
  have hkr' : k*r < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hr.le hk1) hr'
  have hc := Cn_pos hr hr'.le
  have hd := Cn_pos hkr hkr'.le
  have hs := Cn_scale_le hr.le hr'.le hk0.le hk1
  have hmrel : (1-m)*k=m := by rw [hk]; field_simp
  have hcoef : m+(1-m)*k^2=k := by linear_combination (k-1)*hmrel
  have hupper : Real.log 2*delta ≤ k*Cn r := by
    rw [hdelta]
    have ht := mul_le_mul_of_nonneg_left hs hmc.le
    nlinarith only [ht, congrArg (fun x => x*Cn r) hcoef]
  have hdp : 0 < delta := by
    have hp : 0 < m*Cn r+(1-m)*Cn (k*r) := by positivity
    rw [← hdelta] at hp
    exact pos_of_mul_pos_right hp log_two_pos.le
  have hdu : delta ≤ r^2/31 := by
    apply (mul_le_mul_iff_left₀ log_two_pos).mp
    have ht := mul_le_mul_of_nonneg_left (Cn_le_log_mul_sq hr.le hr'.le) hk0.le
    have ht' := mul_le_mul_of_nonneg_right hkmax (mul_nonneg log_two_pos.le (sq_nonneg r))
    nlinarith only [hupper,ht,ht']
  have hw : (1-k+k^2)*(m*Cn r+(1-m)*Cn (k*r)) ≤
      m*Cn r+(1-m)*k^2*Cn (k*r) := by
    have he : m*k=(1-m)*k^2 := by linear_combination -k*hmrel
    have hp : 0 ≤ (1-k)*((1-m)*(k^2*Cn r-Cn (k*r))) :=
      mul_nonneg (by linarith) (mul_nonneg hmc.le (sub_nonneg.mpr hs))
    nlinarith only [hp,congrArg (fun x => (1-k)*Cn r*x) he]
  have hcmin : (931/961 : ℝ) ≤ 1-k+k^2 := by
    have hp : 0 ≤ (1/31-k)*(1-1/31-k) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [hp]
  have hjbound : (4+(1862/2883)*r^2)*delta ≤ j := by
    have hb₁ := mul_le_mul_of_nonneg_left (mean_cost_bonus hr.le hr') hm.le
    have hb₂ := mul_le_mul_of_nonneg_left (mean_cost_bonus hkr.le hkr') hmc.le
    have hwb := mul_le_mul_of_nonneg_left hw (show 0 ≤ (2/3 : ℝ)*r^2 by positivity)
    have hcb := mul_le_mul_of_nonneg_right hcmin
      (show 0 ≤ (2/3 : ℝ)*r^2*(Real.log 2*delta) by positivity)
    rw [← hdelta] at hwb
    apply (mul_le_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hb₁,hb₂,hwb,hcb,hdelta,hj]
  have hg : gamma r*delta ≤ 2*k*r^2/((1+r)*(1+k*r)) := by
    have hgd := mul_le_mul_of_nonneg_left ((le_div_iff₀ log_two_pos).mpr
      (by simpa only [mul_comm] using hupper)) (gamma_pos hr hr'.le).le
    have he : gamma r*(k*Cn r/Real.log 2) = 2*k*r^2/((1+r)*(1+r/31)) := by
      rw [gamma_eq hr hr'.le]
      field_simp [hc.ne',hr.ne',log_two_pos.ne']
    rw [he] at hgd
    apply hgd.trans
    apply div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < (1+r)*(1+k*r))
    have hkm := mul_le_mul_of_nonneg_right hkmax hr.le
    nlinarith only [hkm,hr.le]
  exact ⟨hdp,hdu,hjbound,hg⟩

theorem normalized_alpha {m r k : ℝ} (hm : 0 < m) (hm' : m < 1)
    (hr : 0 ≤ r) (hk : k = m/(1-m)) :
    (m*(1+r)-m*(1-r))^2/(2*(m*(1+r))*(1-m*(1-r))) =
      2*k*r^2/((1+r)*(1+k*r)) := by
  have hmc : 1-m ≠ 0 := by linarith
  have hma : 1-m*(1-r) ≠ 0 := by nlinarith
  have hpr : 1+r ≠ 0 := by positivity
  have he : 1+k*r=(1-m*(1-r))/(1-m) := by rw [hk]; field_simp [hmc]; ring
  rw [he, hk]
  field_simp [hmc,hma,hpr,hm.ne']
  ring

/-- The normalized mean estimates used by the all-entropy small-mean owner. -/
theorem mean_estimates {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : a+b ≤ 1/16) :
    let m := (a+b)/2
    let r := (b-a)/(a+b)
    let delta := H m-(H a+H b)/2
    0 < delta ∧ delta ≤ r^2/31 ∧ (4+(1862/2883)*r^2)*delta ≤ interiorCost a b ∧
      gamma r*delta ≤ (b-a)^2/(2*b*(1-a)) := by
  let m := (a+b)/2
  let r := (b-a)/(a+b)
  let k := m/(1-m)
  have hs0 : 0 < a+b := by linarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hms : m ≤ 1/32 := by dsimp [m]; linarith
  have hm' : m < 1 := by linarith
  have hr : 0 < r := div_pos (by linarith) hs0
  have hr' : r < 1 := (div_lt_one hs0).mpr (by linarith)
  have hkmax : k ≤ 1/31 := (div_le_iff₀ (by linarith : 0 < 1-m)).mpr (by linarith)
  have hae : m*(1-r)=a := by dsimp [m,r]; field_simp [hs0.ne']; ring
  have hbe : m*(1+r)=b := by dsimp [m,r]; field_simp [hs0.ne']; ring
  have hbn : m*(1+r)<1 := by rw [hbe]; exact hb
  have he := normalized_entropy_chain hm hm' hr.le hr' hbn (show k=m/(1-m) from rfl)
  have hc := normalized_cost_chain hm hm' hr.le hr' hbn (show k=m/(1-m) from rfl)
  rw [hae,hbe] at he hc
  have ht := normalized_estimates hm hm' hr hr' (show k=m/(1-m) from rfl) hkmax he hc
  have halpha := normalized_alpha hm hm' hr.le (show k=m/(1-m) from rfl)
  rw [hae,hbe] at halpha
  exact ⟨ht.1,ht.2.1,ht.2.2.1,halpha ▸ ht.2.2.2⟩

end GeneralCK.SmallMean


