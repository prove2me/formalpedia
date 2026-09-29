-- Prove2me | Definitions.Def_CK_GeneralCK_LowInformationMeans
-- name    : CK_GeneralCK_LowInformationMeans
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:36:18.418635+00:00
-- url     : https://prove2.me/theorems/22e5f14e-fb53-4460-bff3-f80616c5d267
-- title:
--   Courtade–Kumar proof module `GeneralCK.LowInformationMeans` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LowInformationMeans` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LowInformationMeans` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LowInformationMeans (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LowInformationMeans.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanMeans
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants

namespace GeneralCK.LowInformation
open Set SmallMean

theorem Cn_upper_sharp {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    Cn r ≤ r^2/2+r^4/(12*(1-r^2)) := by
  let g : ℝ → ℝ := fun r => r^2/2+r^4/(12*(1-r^2))-Cn r
  have hd : ∀ x ∈ Ico (0 : ℝ) 1, HasDerivAt g
      (x+x^3/(3*(1-x^2))+x^5/(6*(1-x^2)^2)-A x) x := by
    intro x hx
    have hn : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    have hh := (((hasDerivAt_id x).pow 2).div_const 2).add
      (((hasDerivAt_id x).pow 4).div
        ((((hasDerivAt_id x).pow 2).const_sub 1).const_mul 12) (by positivity))
    have hc := hh.sub (hasDerivAt_Cn (by linarith [hx.1]) hx.2)
    convert! hc using 1
    simp only [id_eq, Pi.pow_apply]
    field_simp [hn.ne']
    ring
  have hm : MonotoneOn g (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    have ha := A_upper_sharp hx'.1 hx'.2
    have hp : 0 ≤ x^5/(6*(1-x^2)^2) := by have := hx'.1; positivity
    linarith
  have hh := hm (by norm_num : (0 : ℝ) ∈ Ico 0 1) ⟨hr,hr'⟩ hr
  dsimp [g] at hh
  simp only [Cn_zero, zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 4 ≠ 0),
    zero_div, zero_add, sub_zero] at hh
  linarith

theorem Cn_small_ratio {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1/5) :
    (1+r)^2*Cn r ≤ (145/200)*r^2 := by
  have hr1 : r < 1 := by linarith
  have hn : 0 < 1-r^2 := by nlinarith
  have hs : r^2 ≤ 1/25 := by nlinarith
  have hf : r^2/(12*(1-r^2)) ≤ (1/288 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12*(1-r^2))).mpr
    nlinarith only [hs]
  have hc : Cn r ≤ (145/288)*r^2 := by
    have hb := Cn_upper_sharp hr hr1
    have hm := mul_le_mul_of_nonneg_left hf (sq_nonneg r)
    have he : r^2*(r^2/(12*(1-r^2)))=r^4/(12*(1-r^2)) := by ring
    rw [he] at hm
    linarith
  have ht : (1+r)^2 ≤ (36/25 : ℝ) := by nlinarith
  have hb := mul_le_mul ht hc (by linarith [Cn_ge_half_sq hr hr1.le]) (by norm_num : (0 : ℝ) ≤ 36/25)
  nlinarith only [hb]

theorem normalized_bounds {m r k delta j : ℝ}
    (hm : 0 < m) (hm' : m ≤ 1/2) (hr : 0 < r) (hr' : r < 1)
    (hk : k = m/(1-m))
    (hdelta : Real.log 2*delta=m*Cn r+(1-m)*Cn (k*r))
    (hj : Real.log 2*j=2*m*r*A r+2*(1-m)*(k*r)*A (k*r)) :
    0 < delta ∧ Real.log 2*delta ≤ k*Cn r ∧ (4+r^2/2)*delta ≤ j := by
  have hmc : 0 < 1-m := by linarith
  have hk0 : 0 < k := by rw [hk]; positivity
  have hk1 : k ≤ 1 := by rw [hk]; apply (div_le_one hmc).mpr; linarith
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
    nlinarith only [ht,congrArg (fun x => x*Cn r) hcoef]
  have hdp : 0 < delta := by
    have hp : 0 < m*Cn r+(1-m)*Cn (k*r) := by positivity
    rw [← hdelta] at hp
    exact pos_of_mul_pos_right hp log_two_pos.le
  have hw : (1-k+k^2)*(m*Cn r+(1-m)*Cn (k*r)) ≤ m*Cn r+(1-m)*k^2*Cn (k*r) := by
    have he : m*k=(1-m)*k^2 := by linear_combination -k*hmrel
    have hp : 0 ≤ (1-k)*((1-m)*(k^2*Cn r-Cn (k*r))) :=
      mul_nonneg (by linarith) (mul_nonneg hmc.le (sub_nonneg.mpr hs))
    nlinarith only [hp,congrArg (fun x => (1-k)*Cn r*x) he]
  have hcmin : (3/4 : ℝ) ≤ 1-k+k^2 := by nlinarith only [sq_nonneg (k-1/2)]
  have hjbound : (4+r^2/2)*delta ≤ j := by
    have hb₁ := mul_le_mul_of_nonneg_left (mean_cost_bonus hr.le hr') hm.le
    have hb₂ := mul_le_mul_of_nonneg_left (mean_cost_bonus hkr.le hkr') hmc.le
    have hwb := mul_le_mul_of_nonneg_left hw (show 0 ≤ (2/3 : ℝ)*r^2 by positivity)
    have hcb := mul_le_mul_of_nonneg_right hcmin
      (show 0 ≤ (2/3 : ℝ)*r^2*(Real.log 2*delta) by positivity)
    rw [← hdelta] at hwb
    apply (mul_le_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hb₁,hb₂,hwb,hcb,hdelta,hj]
  exact ⟨hdp,hupper,hjbound⟩

theorem normalized_low_alpha {r k delta : ℝ} (hr : 0 < r) (hr' : r ≤ 1/5)
    (hk : 0 < k) (hk' : k ≤ 1) (hd : 0 ≤ delta)
    (hupper : Real.log 2*delta ≤ k*Cn r) :
    (19/10)*delta ≤ 2*k*r^2/((1+r)*(1+k*r)) := by
  have hdenp : 0 < (1+r)*(1+k*r) := by positivity
  have hden : (1+r)*(1+k*r) ≤ (1+r)^2 := by
    have hm := mul_le_of_le_one_left hr.le hk'
    nlinarith only [mul_le_mul_of_nonneg_left hm (show 0 ≤ 1+r by linarith)]
  have hp := mul_le_mul_of_nonneg_right hden (mul_nonneg log_two_pos.le hd)
  have ht := mul_le_mul_of_nonneg_left hupper (sq_nonneg (1+r))
  have hc := mul_le_mul_of_nonneg_left (Cn_small_ratio hr.le hr') hk.le
  have he : ((80*Real.log 2)/29)*delta ≤ 2*k*r^2/((1+r)*(1+k*r)) := by
    apply (le_div_iff₀ hdenp).mpr
    nlinarith only [hp,ht,hc]
  have hcoef : (19/10 : ℝ) ≤ (80*Real.log 2)/29 := by
    have hl := Certificates.Mixed.log_two_gt_69
    linarith only [hl]
  exact (mul_le_mul_of_nonneg_right hcoef hd).trans he

theorem mean_normalization {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : a+b ≤ 1) :
    let m := (a+b)/2
    let r := (b-a)/(a+b)
    let k := m/(1-m)
    let delta := H m-(H a+H b)/2
    0 < delta ∧ Real.log 2*delta ≤ k*Cn r ∧ (4+r^2/2)*delta ≤ interiorCost a b := by
  let m := (a+b)/2
  let r := (b-a)/(a+b)
  let k := m/(1-m)
  have hs0 : 0 < a+b := by linarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hmhalf : m ≤ 1/2 := by dsimp [m]; linarith
  have hm' : m < 1 := by linarith
  have hr : 0 < r := div_pos (by linarith) hs0
  have hr' : r < 1 := (div_lt_one hs0).mpr (by linarith)
  have hae : m*(1-r)=a := by dsimp [m,r]; field_simp [hs0.ne']; ring
  have hbe : m*(1+r)=b := by dsimp [m,r]; field_simp [hs0.ne']; ring
  have hbn : m*(1+r)<1 := by rw [hbe]; exact hb
  have he := normalized_entropy_chain hm hm' hr.le hr' hbn (show k=m/(1-m) from rfl)
  have hc := normalized_cost_chain hm hm' hr.le hr' hbn (show k=m/(1-m) from rfl)
  rw [hae,hbe] at he hc
  exact normalized_bounds hm hmhalf hr hr' (show k=m/(1-m) from rfl) he hc

/-- Uniform mean-cost improvement in the canonical orientation. -/
theorem mean_estimates {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : a+b ≤ 1) :
    let r := (b-a)/(a+b)
    let delta := H ((a+b)/2)-(H a+H b)/2
    0 < delta ∧ (4+r^2/2)*delta ≤ interiorCost a b := by
  have ht := mean_normalization ha hab hb hs
  exact ⟨ht.1,ht.2.2⟩

/-- Close canonical means have a sufficiently large log-sum slope. -/
theorem low_ratio_alpha {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : a+b ≤ 1) (hrmax : (b-a)/(a+b) ≤ 1/5) :
    (19/10)*(H ((a+b)/2)-(H a+H b)/2) ≤ (b-a)^2/(2*b*(1-a)) := by
  let m := (a+b)/2
  let r := (b-a)/(a+b)
  let k := m/(1-m)
  have hs0 : 0 < a+b := by linarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hmhalf : m ≤ 1/2 := by dsimp [m]; linarith
  have hm' : m < 1 := by linarith
  have hr : 0 < r := div_pos (by linarith) hs0
  have hk : 0 < k := by dsimp [k]; positivity
  have hk' : k ≤ 1 := by apply (div_le_one (by linarith : 0 < 1-m)).mpr; linarith
  have hae : m*(1-r)=a := by dsimp [m,r]; field_simp [hs0.ne']; ring
  have hbe : m*(1+r)=b := by dsimp [m,r]; field_simp [hs0.ne']; ring
  have ht := mean_normalization ha hab hb hs
  have haeq := normalized_alpha hm hm' hr.le (show k=m/(1-m) from rfl)
  rw [hae,hbe] at haeq
  rw [haeq]
  exact normalized_low_alpha hr hrmax hk hk' ht.1.le ht.2.1

end GeneralCK.LowInformation


