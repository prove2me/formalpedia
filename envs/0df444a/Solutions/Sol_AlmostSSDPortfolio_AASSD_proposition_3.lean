-- Prove2me | solution 1 for AlmostSSDPortfolio.AASSD.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:24:41.88698+00:00
-- url     : https://prove2.me/submissions/bb1c81a6-7e26-4828-bd74-b7448c90b29b

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

section helpers
variable {n T Tb : ℕ}

lemma lpm_continuous {ι : Type*} [Fintype ι] (p v : ι → ℝ) : Continuous (lpm p v) := by
  unfold lpm
  fun_prop

lemma lpm_convex {ι : Type*} [Fintype ι] (p v : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    lpm p v (a * x + b * y) ≤ a * lpm p v x + b * lpm p v y := by
  unfold lpm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  have h1 : max (a * x + b * y - v t) 0 ≤ a * max (x - v t) 0 + b * max (y - v t) 0 := by
    have e : a * x + b * y - v t = a * (x - v t) + b * (y - v t) := by
      linear_combination (v t) * hab
    apply max_le
    · rw [e]
      linarith [mul_le_mul_of_nonneg_left (le_max_left (x - v t) 0) ha,
        mul_le_mul_of_nonneg_left (le_max_left (y - v t) 0) hb]
    · have := mul_nonneg ha (le_max_right (x - v t) 0)
      have := mul_nonneg hb (le_max_right (y - v t) 0)
      linarith
  calc p t * max (a * x + b * y - v t) 0 ≤ p t * (a * max (x - v t) 0 + b * max (y - v t) 0) :=
        mul_le_mul_of_nonneg_left h1 (hp t)
    _ = _ := by ring

variable {S : Setting n T Tb}

lemma F2_continuous (lam : Fin n → ℝ) : Continuous (S.F2 lam) := lpm_continuous _ _
lemma G2_continuous : Continuous S.G2 := lpm_continuous _ _

lemma interp_left (D : Discretization S) (lam : Fin n → ℝ) (s : Fin D.K) :
    S.F2 lam (D.d s.castSucc) +
      (S.F2 lam (D.d s.succ) - S.F2 lam (D.d s.castSucc)) /
        (D.d s.succ - D.d s.castSucc) * (D.d s.castSucc - D.d s.castSucc) =
      S.F2 lam (D.d s.castSucc) := by simp

lemma dlt (D : Discretization S) (s : Fin D.K) : D.d s.castSucc < D.d s.succ :=
  D.strictMono (Fin.castSucc_lt_succ)

lemma interp_right (D : Discretization S) (lam : Fin n → ℝ) (s : Fin D.K) :
    S.F2 lam (D.d s.castSucc) +
      (S.F2 lam (D.d s.succ) - S.F2 lam (D.d s.castSucc)) /
        (D.d s.succ - D.d s.castSucc) * (D.d s.succ - D.d s.castSucc) =
      S.F2 lam (D.d s.succ) := by
  have := (sub_pos.2 (dlt D s)).ne'
  field_simp
  ring

lemma hatF_eq (D : Discretization S) (lam : Fin n → ℝ) (s : Fin D.K) (z : ℝ)
    (hz : z ∈ Icc (D.d s.castSucc) (D.d s.succ)) :
    D.hatF2 lam z = S.F2 lam (D.d s.castSucc) +
      (S.F2 lam (D.d s.succ) - S.F2 lam (D.d s.castSucc)) /
        (D.d s.succ - D.d s.castSucc) * (z - D.d s.castSucc) := by
  have hex : ∃ s : Fin D.K, z ∈ Icc (D.d s.castSucc) (D.d s.succ) := ⟨s, hz⟩
  unfold Discretization.hatF2
  rw [dif_pos hex]
  set s' := hex.choose with hs'
  have hz' : z ∈ Icc (D.d s'.castSucc) (D.d s'.succ) := hex.choose_spec
  by_cases hss : s' = s
  · rw [hss]
  · rcases lt_or_gt_of_ne hss with h | h
    · -- s' < s
      have hle : s'.succ ≤ s.castSucc := Fin.succ_le_castSucc_iff.2 h
      have hle' : D.d s'.succ ≤ D.d s.castSucc := D.strictMono.monotone hle
      have e1 : z = D.d s'.succ := le_antisymm hz'.2 (hle'.trans hz.1)
      have e2 : z = D.d s.castSucc := le_antisymm (e1.le.trans hle') hz.1
      have e3 : D.d s'.succ = D.d s.castSucc := e1.symm.trans e2
      have e4 : s'.succ = s.castSucc := D.strictMono.injective e3
      have L : S.F2 lam (D.d s'.castSucc) +
          (S.F2 lam (D.d s'.succ) - S.F2 lam (D.d s'.castSucc)) /
            (D.d s'.succ - D.d s'.castSucc) * (z - D.d s'.castSucc) = S.F2 lam (D.d s'.succ) := by
        rw [e1]; exact interp_right D lam s'
      have R : S.F2 lam (D.d s.castSucc) +
          (S.F2 lam (D.d s.succ) - S.F2 lam (D.d s.castSucc)) /
            (D.d s.succ - D.d s.castSucc) * (z - D.d s.castSucc) = S.F2 lam (D.d s.castSucc) := by
        rw [e2]; simp
      rw [L, R, e4]
    · have hle : s.succ ≤ s'.castSucc := Fin.succ_le_castSucc_iff.2 h
      have hle' : D.d s.succ ≤ D.d s'.castSucc := D.strictMono.monotone hle
      have e1 : z = D.d s.succ := le_antisymm hz.2 (hle'.trans hz'.1)
      have e2 : z = D.d s'.castSucc := le_antisymm (e1.le.trans hle') hz'.1
      have e3 : D.d s.succ = D.d s'.castSucc := e1.symm.trans e2
      have e4 : s.succ = s'.castSucc := D.strictMono.injective e3
      have L : S.F2 lam (D.d s'.castSucc) +
          (S.F2 lam (D.d s'.succ) - S.F2 lam (D.d s'.castSucc)) /
            (D.d s'.succ - D.d s'.castSucc) * (z - D.d s'.castSucc) = S.F2 lam (D.d s'.castSucc) := by
        rw [e2]; simp
      have R : S.F2 lam (D.d s.castSucc) +
          (S.F2 lam (D.d s.succ) - S.F2 lam (D.d s.castSucc)) /
            (D.d s.succ - D.d s.castSucc) * (z - D.d s.castSucc) = S.F2 lam (D.d s.succ) := by
        rw [e1]; exact interp_right D lam s
      rw [L, R, e4]

lemma prop1_aux (D : Discretization S) (hS : S.Standing) (lam : Fin n → ℝ)
    (x : ℝ) : S.F2 lam x ≤ D.hatF2 lam x := by
  have hp : ∀ t, 0 ≤ S.p t := fun t => hS.2.1.1 t
  by_cases hex : ∃ s : Fin D.K, x ∈ Icc (D.d s.castSucc) (D.d s.succ)
  · obtain ⟨s, hs⟩ := hex
    rw [hatF_eq D lam s x hs]
    have hlt := sub_pos.2 (dlt D s)
    set l := D.d s.castSucc
    set r := D.d s.succ
    have hθ0 : 0 ≤ (x - l) / (r - l) := div_nonneg (sub_nonneg.2 hs.1) hlt.le
    have hθ1 : 0 ≤ 1 - (x - l) / (r - l) := by
      rw [sub_nonneg, div_le_one hlt]; linarith [hs.2]
    have hx : x = (1 - (x - l) / (r - l)) * l + ((x - l) / (r - l)) * r := by
      field_simp; ring
    have := lpm_convex S.p (S.ret lam) hp (x := l) (y := r) hθ1 hθ0 (by ring)
    rw [← hx] at this
    have e : S.F2 lam l + (S.F2 lam r - S.F2 lam l) / (r - l) * (x - l) =
        (1 - (x - l) / (r - l)) * S.F2 lam l + ((x - l) / (r - l)) * S.F2 lam r := by
      field_simp; ring
    rw [e]
    exact this
  · unfold Discretization.hatF2
    rw [dif_neg hex]

end helpers

lemma lin_int (β c x y : ℝ) : ∫ z in x..y, β * (z - c) = β * ((y - c) ^ 2 - (x - c) ^ 2) / 2 := by
  have : ∀ z : ℝ, HasDerivAt (fun z => β * (z - c) ^ 2 / 2) (β * (z - c)) z := by
    intro z
    have h := ((hasDerivAt_id z).sub_const c).pow 2
    have h2 := (h.const_mul β).div_const 2
    exact h2.congr_deriv (by simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => this z)]
  · ring
  · exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _

/-- the linear function from `ul` at `l` to `ur` at `r` -/
noncomputable def lin (ul ur l r z : ℝ) : ℝ := ul + (ur - ul) / (r - l) * (z - l)

lemma lin_eq (ul ur l r z : ℝ) (h : l < r) :
    lin ul ur l r z = (ul * (r - z) + ur * (z - l)) / (r - l) := by
  have : r - l ≠ 0 := (sub_pos.2 h).ne'
  unfold lin; field_simp; ring

lemma lin_nonneg {ul ur l r z : ℝ} (h : l < r) (hl : 0 ≤ ul) (hr : 0 ≤ ur)
    (hz : z ∈ Icc l r) : 0 ≤ lin ul ur l r z := by
  rw [lin_eq _ _ _ _ _ h]
  apply div_nonneg _ (sub_pos.2 h).le
  have := hz.1; have := hz.2
  have := mul_nonneg hl (sub_nonneg.2 hz.2)
  have := mul_nonneg hr (sub_nonneg.2 hz.1)
  linarith

lemma lin_nonpos {ul ur l r z : ℝ} (h : l < r) (hl : ul ≤ 0) (hr : ur ≤ 0)
    (hz : z ∈ Icc l r) : lin ul ur l r z ≤ 0 := by
  have := lin_nonneg h (neg_nonneg.2 hl) (neg_nonneg.2 hr) hz
  unfold lin at *
  have e : -ul + (-ur - -ul) / (r - l) * (z - l) = -(ul + (ur - ul) / (r - l) * (z - l)) := by
    ring
  rw [e] at this
  linarith

lemma lin_cont (ul ur l r : ℝ) : Continuous fun z => max (lin ul ur l r z) 0 := by
  unfold lin; fun_prop

lemma lin_integral (ul ur l r : ℝ) (h : l < r) :
    ∫ z in l..r, max (lin ul ur l r z) 0 =
      if ul ≤ 0 ∧ ur ≤ 0 then 0
      else if ul ≤ 0 ∧ 0 ≤ ur then (r - l) * ur ^ 2 / (2 * (ur - ul))
      else if 0 ≤ ul ∧ ur ≤ 0 then (r - l) * ul ^ 2 / (2 * (ul - ur))
      else (ur + ul) * ((r - l) / 2) := by
  have hrl : 0 < r - l := sub_pos.2 h
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun z => max (lin ul ur l r z) 0) volume x y :=
    fun x y => (lin_cont ul ur l r).intervalIntegrable _ _
  split_ifs with c1 c2 c3
  · rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro z hz
      rw [uIcc_of_le h.le] at hz
      simp only [max_eq_right (lin_nonpos h c1.1 c1.2 hz)]
  · -- ul ≤ 0 ≤ ur, ur > 0
    have hur : 0 < ur := by
      rcases lt_or_eq_of_le c2.2 with h' | h'
      · exact h'
      · exfalso; apply c1; exact ⟨c2.1, h'.symm ▸ le_rfl⟩
    have hd : 0 < ur - ul := by linarith [c2.1]
    set c := l + (r - l) * (-ul) / (ur - ul) with hc
    have hcl : l ≤ c := by
      have : 0 ≤ (r - l) * (-ul) / (ur - ul) :=
        div_nonneg (mul_nonneg hrl.le (by linarith [c2.1])) hd.le
      linarith
    have hcr : c ≤ r := by
      have : (r - l) * (-ul) / (ur - ul) ≤ (r - l) := by
        rw [div_le_iff₀ hd]; nlinarith [c2.1]
      linarith
    set m := (ur - ul) / (r - l) with hm
    have hmpos : 0 < m := div_pos hd hrl
    have hlin : ∀ z, lin ul ur l r z = m * (z - c) := by
      intro z
      unfold lin
      rw [hc, hm]
      field_simp
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint l c) (hint c r)]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (a := l) (b := c)]
    swap
    · intro z hz
      rw [uIcc_of_le hcl] at hz
      simp only [hlin]
      exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hmpos.le (by linarith [hz.2]))
    rw [intervalIntegral.integral_congr (g := fun z => m * (z - c)) (a := c) (b := r)]
    swap
    · intro z hz
      rw [uIcc_of_le hcr] at hz
      simp only [hlin]
      exact max_eq_left (mul_nonneg hmpos.le (by linarith [hz.1]))
    rw [lin_int]
    simp only [intervalIntegral.integral_zero, zero_add]
    have e1 : r - c = (r - l) * ur / (ur - ul) := by
      rw [hc]; field_simp; ring
    have e2 : m * (r - c) = ur := by
      rw [e1, hm]; field_simp
    have : m * ((r - c) ^ 2 - (c - c) ^ 2) / 2 = (m * (r - c)) * (r - c) / 2 := by ring
    rw [this, e2, e1]
    field_simp
  · -- ul ≥ 0 ≥ ur, ul > 0
    have hul : 0 < ul := by
      rcases lt_or_eq_of_le c3.1 with h' | h'
      · exact h'
      · exfalso; apply c1; exact ⟨h'.symm ▸ le_rfl, c3.2⟩
    have hd : 0 < ul - ur := by linarith [c3.2]
    set c := l + (r - l) * ul / (ul - ur) with hc
    have hcl : l ≤ c := by
      have : 0 ≤ (r - l) * ul / (ul - ur) :=
        div_nonneg (mul_nonneg hrl.le hul.le) hd.le
      linarith
    have hcr : c ≤ r := by
      have : (r - l) * ul / (ul - ur) ≤ (r - l) := by
        rw [div_le_iff₀ hd]; nlinarith [c3.2]
      linarith
    set m := (ur - ul) / (r - l) with hm
    have hmneg : m < 0 := div_neg_of_neg_of_pos (by linarith) hrl
    have hlin : ∀ z, lin ul ur l r z = m * (z - c) := by
      intro z
      unfold lin
      rw [hc, hm]
      field_simp
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint l c) (hint c r)]
    rw [intervalIntegral.integral_congr (g := fun z => m * (z - c)) (a := l) (b := c)]
    swap
    · intro z hz
      rw [uIcc_of_le hcl] at hz
      simp only [hlin]
      exact max_eq_left (mul_nonneg_of_nonpos_of_nonpos hmneg.le (by linarith [hz.2]))
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (a := c) (b := r)]
    swap
    · intro z hz
      rw [uIcc_of_le hcr] at hz
      simp only [hlin]
      exact max_eq_right (mul_nonpos_of_nonpos_of_nonneg hmneg.le (by linarith [hz.1]))
    rw [lin_int]
    simp only [intervalIntegral.integral_zero, add_zero]
    have e1 : c - l = (r - l) * ul / (ul - ur) := by
      rw [hc]; ring
    have e2 : m * (c - l) = -ul := by
      rw [e1, hm]; field_simp; ring
    have : m * ((c - c) ^ 2 - (l - c) ^ 2) / 2 = -(m * (c - l)) * (c - l) / 2 := by ring
    rw [this, e2, e1]
    field_simp
  · -- both positive
    have hul : 0 < ul := by
      by_contra hh; push Not at hh
      have : 0 < ur := by
        by_contra h2; push Not at h2; exact c1 ⟨hh, h2⟩
      exact c2 ⟨hh, this.le⟩
    have hur : 0 < ur := by
      by_contra hh; push Not at hh
      exact c3 ⟨hul.le, hh⟩
    rw [intervalIntegral.integral_congr (g := fun z => ul + (ur - ul) / (r - l) * (z - l))]
    swap
    · intro z hz
      rw [uIcc_of_le h.le] at hz
      exact max_eq_left (lin_nonneg h hul.le hur.le hz)
    rw [intervalIntegral.integral_add (f := fun _ => ul) (g := fun z => (ur - ul) / (r - l) * (z - l))
      (by simp) ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)]
    rw [lin_int]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring


section part3
variable {n T Tb : ℕ} {S : Setting n T Tb}

lemma G2_affine (D : Discretization S) (s : Fin D.K) :
    ∃ α β : ℝ, ∀ z ∈ Icc (D.d s.castSucc) (D.d s.succ), S.G2 z = α + β * z := by
  have key : ∀ t', ∃ c e : ℝ, ∀ z ∈ Icc (D.d s.castSucc) (D.d s.succ),
      max (z - S.bv t') 0 = c * z + e := by
    intro t'
    obtain ⟨k, hk⟩ := D.covers t'
    by_cases h : k ≤ s.castSucc
    · refine ⟨1, -S.bv t', fun z hz => ?_⟩
      have h1 : D.d k ≤ D.d s.castSucc := D.strictMono.monotone h
      rw [hk] at h1
      rw [max_eq_left (by linarith [hz.1])]; ring
    · push Not at h
      have h2 : s.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 h
      have h1 : D.d s.succ ≤ D.d k := D.strictMono.monotone h2
      rw [hk] at h1
      refine ⟨0, 0, fun z hz => ?_⟩
      rw [max_eq_right (by linarith [hz.2])]; ring
  choose c e hce using key
  refine ⟨∑ t', S.q t' * e t', ∑ t', S.q t' * c t', fun z hz => ?_⟩
  unfold Setting.G2 lpm
  have : ∀ t', S.q t' * max (z - S.bv t') 0 = S.q t' * c t' * z + S.q t' * e t' := by
    intro t'; rw [hce t' z hz]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

lemma diff_eq (D : Discretization S) (lam : Fin n → ℝ) (s : Fin D.K) (z : ℝ)
    (hz : z ∈ Icc (D.d s.castSucc) (D.d s.succ)) :
    D.hatF2 lam z - S.G2 z =
      lin (S.F2 lam (D.d s.castSucc) - S.G2 (D.d s.castSucc))
        (S.F2 lam (D.d s.succ) - S.G2 (D.d s.succ)) (D.d s.castSucc) (D.d s.succ) z := by
  obtain ⟨α, β, hG⟩ := G2_affine D s
  have hl : D.d s.castSucc ∈ Icc (D.d s.castSucc) (D.d s.succ) := ⟨le_rfl, (dlt D s).le⟩
  have hr : D.d s.succ ∈ Icc (D.d s.castSucc) (D.d s.succ) := ⟨(dlt D s).le, le_rfl⟩
  rw [hatF_eq D lam s z hz, hG z hz, hG _ hl, hG _ hr]
  have := (sub_pos.2 (dlt D s)).ne'
  unfold lin
  field_simp
  ring

lemma violation_eq (fl fr gl gr l r : ℝ) (h : l < r) :
    ∫ z in l..r, max (lin (fl - gl) (fr - gr) l r z) 0 = violation fl fr gl gr l r := by
  rw [lin_integral _ _ _ _ h]
  unfold violation
  simp only [sub_nonpos, sub_nonneg]
  have e1 : fr - gr - (fl - gl) = fr - gr + gl - fl := by ring
  have e2 : fl - gl - (fr - gr) = gr - fr + fl - gl := by ring
  rw [e1, e2]
  split_ifs <;> first | rfl | ring

lemma piece_integral (D : Discretization S) (lam : Fin n → ℝ) (s : Fin D.K) :
    ∫ z in D.d s.castSucc..D.d s.succ, max (D.hatF2 lam z - S.G2 z) 0 = D.A lam s := by
  rw [intervalIntegral.integral_congr (g := fun z => max (lin (S.F2 lam (D.d s.castSucc) - S.G2 (D.d s.castSucc))
        (S.F2 lam (D.d s.succ) - S.G2 (D.d s.succ)) (D.d s.castSucc) (D.d s.succ) z) 0)]
  · exact violation_eq _ _ _ _ _ _ (dlt D s)
  · intro z hz
    rw [uIcc_of_le (dlt D s).le] at hz
    simp only [diff_eq D lam s z hz]

lemma piece_integrableOn (D : Discretization S) (lam : Fin n → ℝ) (s : Fin D.K) :
    IntegrableOn (fun z => max (D.hatF2 lam z - S.G2 z) 0) (Icc (D.d s.castSucc) (D.d s.succ)) := by
  refine ((lin_cont (S.F2 lam (D.d s.castSucc) - S.G2 (D.d s.castSucc))
        (S.F2 lam (D.d s.succ) - S.G2 (D.d s.succ)) (D.d s.castSucc) (D.d s.succ)).continuousOn.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
  intro z hz
  simp only [diff_eq D lam s z hz]

/-- extension of the grid to a sequence indexed by naturals -/
noncomputable def dd (D : Discretization S) (k : ℕ) : ℝ :=
  if h : k < D.K + 1 then D.d ⟨k, h⟩ else S.b

lemma dd_castSucc (D : Discretization S) (s : Fin D.K) : dd D s.val = D.d s.castSucc := by
  unfold dd; rw [dif_pos (by omega)]; rfl

lemma dd_succ (D : Discretization S) (s : Fin D.K) : dd D (s.val + 1) = D.d s.succ := by
  unfold dd; rw [dif_pos (by omega)]; rfl

lemma dd_zero (D : Discretization S) : dd D 0 = S.a := by
  unfold dd; rw [dif_pos (by omega)]; exact D.first

lemma dd_K (D : Discretization S) : dd D D.K = S.b := by
  unfold dd; rw [dif_pos (by omega)]; exact D.last

lemma intInt_pieces (D : Discretization S) (lam : Fin n → ℝ) :
    ∀ m ≤ D.K, IntervalIntegrable (fun z => max (D.hatF2 lam z - S.G2 z) 0) volume (dd D 0) (dd D m) := by
  intro m
  induction m with
  | zero => intro _; exact IntervalIntegrable.refl
  | succ m ih =>
    intro hm
    refine (ih (by omega)).trans ?_
    have hs : m < D.K := by omega
    have := piece_integrableOn D lam ⟨m, hs⟩
    rw [← dd_castSucc D ⟨m, hs⟩, ← dd_succ D ⟨m, hs⟩] at this
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by
      rw [dd_castSucc D ⟨m, hs⟩, dd_succ D ⟨m, hs⟩] ; exact (dlt D ⟨m, hs⟩).le)).2 this

lemma sum_pieces (D : Discretization S) (lam : Fin n → ℝ) :
    ∫ z in S.a..S.b, max (D.hatF2 lam z - S.G2 z) 0 = ∑ s, D.A lam s := by
  have := intervalIntegral.sum_integral_adjacent_intervals (f := fun z => max (D.hatF2 lam z - S.G2 z) 0)
    (μ := volume) (a := dd D) (n := D.K) (by
      intro k hk
      have h1 := piece_integrableOn D lam ⟨k, hk⟩
      rw [← dd_castSucc D ⟨k, hk⟩, ← dd_succ D ⟨k, hk⟩] at h1
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by
        rw [dd_castSucc D ⟨k, hk⟩, dd_succ D ⟨k, hk⟩]; exact (dlt D ⟨k, hk⟩).le)).2 h1)
  rw [dd_zero, dd_K] at this
  rw [← this, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro s _
  rw [dd_castSucc, dd_succ]
  exact piece_integral D lam s

lemma cover (D : Discretization S) (hab : S.a < S.b) (z : ℝ) (hz : z ∈ Icc S.a S.b) :
    ∃ s : Fin D.K, z ∈ Icc (D.d s.castSucc) (D.d s.succ) := by
  have hK : 0 < D.K := by
    by_contra h0
    have : D.K = 0 := by omega
    have h1 := D.last
    have h2 := D.first
    have : (Fin.last D.K) = 0 := Fin.ext (by simp [this])
    rw [this, h2] at h1
    linarith
  have hex : ∃ k, z ≤ dd D k := ⟨D.K, by rw [dd_K]; exact hz.2⟩
  classical
  set k := Nat.find hex with hk
  have hkK : k ≤ D.K := Nat.find_min' hex (by rw [dd_K]; exact hz.2)
  have hzk : z ≤ dd D k := Nat.find_spec hex
  by_cases h0 : k = 0
  · have : z ≤ S.a := by rw [h0, dd_zero] at hzk; exact hzk
    have hza : z = S.a := le_antisymm this hz.1
    obtain ⟨s0, hs0⟩ : ∃ s0 : Fin D.K, s0 = ⟨0, hK⟩ := ⟨_, rfl⟩
    refine ⟨s0, ?_⟩
    refine ⟨?_, ?_⟩
    · show D.d s0.castSucc ≤ z
      have : D.d s0.castSucc = S.a := by
        rw [← dd_castSucc D s0, hs0, dd_zero]
      rw [this, hza]
    · show z ≤ D.d s0.succ
      have h1 : D.d s0.castSucc ≤ D.d s0.succ := (dlt D s0).le
      have : D.d s0.castSucc = S.a := by
        rw [← dd_castSucc D s0, hs0, dd_zero]
      linarith
  · have hk1 : k - 1 < D.K := by omega
    refine ⟨⟨k - 1, hk1⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · have hnot : ¬ z ≤ dd D (k - 1) := Nat.find_min hex (by omega)
      push Not at hnot
      rw [← dd_castSucc D ⟨k - 1, hk1⟩] 
      exact hnot.le
    · have : dd D (k - 1 + 1) = D.d (Fin.succ ⟨k - 1, hk1⟩) := dd_succ D ⟨k - 1, hk1⟩
      rw [← this]
      have e : k - 1 + 1 = k := by omega
      rw [e]; exact hzk

lemma hatS2_meas (D : Discretization S) (hab : S.a < S.b) (lam : Fin n → ℝ) :
    MeasurableSet (D.hatS2 lam) := by
  have : D.hatS2 lam = ⋃ s : Fin D.K, (Icc (D.d s.castSucc) (D.d s.succ) ∩
      {t | S.G2 t < S.F2 lam (D.d s.castSucc) +
        (S.F2 lam (D.d s.succ) - S.F2 lam (D.d s.castSucc)) /
          (D.d s.succ - D.d s.castSucc) * (t - D.d s.castSucc)}) := by
    ext t
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hI, hlt⟩
      obtain ⟨s, hs⟩ := cover D hab t hI
      refine ⟨s, hs, ?_⟩
      rw [← hatF_eq D lam s t hs]; exact hlt
    · rintro ⟨s, hs, hlt⟩
      rw [← hatF_eq D lam s t hs] at hlt
      refine ⟨⟨?_, ?_⟩, hlt⟩
      · have h1 : D.d 0 ≤ D.d s.castSucc := D.strictMono.monotone (Fin.zero_le _)
        rw [D.first] at h1; linarith [hs.1]
      · have h1 : D.d s.succ ≤ D.d (Fin.last D.K) := D.strictMono.monotone (Fin.le_last _)
        rw [D.last] at h1; linarith [hs.2]
      
  rw [this]
  refine MeasurableSet.iUnion (fun s => measurableSet_Icc.inter ?_)
  exact measurableSet_lt G2_continuous.measurable
    (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).measurable

lemma hatS2_integral (D : Discretization S) (hab : S.a < S.b) (lam : Fin n → ℝ) :
    ∫ t in D.hatS2 lam, (D.hatF2 lam t - S.G2 t) =
      ∫ t in Icc S.a S.b, max (D.hatF2 lam t - S.G2 t) 0 := by
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero (s := D.hatS2 lam) (t := Icc S.a S.b)
    measurableSet_Icc (fun t ht => ht.1) (by
      intro t ht
      have : ¬ S.G2 t < D.hatF2 lam t := fun h => ht.2 ⟨ht.1, h⟩
      exact max_eq_right (by linarith [not_lt.1 this]))]
  exact setIntegral_congr_fun (hatS2_meas D hab lam) (fun t ht => (max_eq_left (by linarith [ht.2])).symm)

theorem prop3_aux (hS : S.Standing) (D : Discretization S) (lam : Fin n → ℝ) :
    ∫ t in D.hatS2 lam, (D.hatF2 lam t - S.G2 t) = ∑ s, D.A lam s := by
  rw [hatS2_integral D hS.1 lam, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hS.1.le]
  exact sum_pieces D lam

end part3

end AlmostSSDPortfolio.AASSD

open AlmostSSDPortfolio.AASSD

theorem solution {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∫ t in D.hatS2 lam, (D.hatF2 lam t - S.G2 t) = ∑ s, D.A lam s := prop3_aux hS D lam
