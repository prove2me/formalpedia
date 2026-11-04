-- Prove2me | solution 1 for AdvSellUpgrade.Online.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:49:17.955919+00:00
-- url     : https://prove2.me/submissions/f80ef3c2-cf42-441f-a851-fc4e6cdd7b5e

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting
import Theorems.Thm_AdvSellUpgrade_Online_prop3_cutoff_problem
import Theorems.Thm_AdvSellUpgrade_Online_cutoff_order

namespace Aux_ASUT1
open AdvSellUpgrade.Online

lemma psi_eq (mu cbar lam c : ℝ) (hlam : 0 < lam) (hml : lam < mu) (hcb : 0 < cbar)
    (hc : 0 ≤ c) :
    c * (WR mu cbar lam c - WF mu cbar lam c) =
      c * lam ^ 2 * cbar / (mu * (mu - lam) * (cbar * (mu - lam) + lam * c)) := by
  have hmu : 0 < mu := by linarith
  have h1 : mu - lam ≠ 0 := by intro h; linarith
  have h2 : 0 < cbar * (mu - lam) + lam * c := by
    have : 0 < cbar * (mu - lam) := mul_pos hcb (by linarith)
    nlinarith
  have h3 : mu - (1 - c / cbar) * lam ≠ 0 := by
    have : mu - (1 - c / cbar) * lam = (cbar * (mu - lam) + lam * c) / cbar := by
      field_simp; ring
    rw [this]; exact (div_pos h2 hcb).ne'
  unfold WR WF
  field_simp
  ring

/-- Quadratic growth of the single-rate revenue gap, in the cutoff and in the price gap. -/
lemma gap (mu cbar lam c : ℝ) (hlam : 0 < lam) (hml : lam < mu) (hcb : 0 < cbar)
    (hc0 : 0 ≤ c) (hc1 : c ≤ cbar) :
    lam ^ 2 / (mu ^ 2 * (mu - lam) * cbar) * (c - cFn mu cbar lam) ^ 2 ≤
        piFn mu cbar lam - c * (WR mu cbar lam c - WF mu cbar lam c) * (1 - c / cbar) ∧
    mu ^ 2 * (mu - lam) / (lam ^ 2 * cbar) *
        (c * (WR mu cbar lam c - WF mu cbar lam c) - pFn mu cbar lam) ^ 2 ≤
        piFn mu cbar lam - c * (WR mu cbar lam c - WF mu cbar lam c) * (1 - c / cbar) := by
  have hmu : 0 < mu := by linarith
  have hml' : 0 < mu - lam := by linarith
  rw [psi_eq mu cbar lam c hlam hml hcb hc0]
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (mu * (mu - lam)) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = mu * (mu - lam) := by rw [hsdef]; exact Real.sq_sqrt (by positivity)
  have hs_lo : mu - lam < s := by
    rw [hsdef, Real.lt_sqrt hml'.le]
    nlinarith
  have hs_hi : s < mu := by
    rw [hsdef, Real.sqrt_lt' hmu]
    nlinarith
  have hs0 : 0 < s := by linarith
  have hsq : Real.sqrt mu * Real.sqrt (mu - lam) = s := by
    rw [hsdef, Real.sqrt_mul hmu.le]
  have e5 : (Real.sqrt mu - Real.sqrt (mu - lam)) ^ 2 = 2 * mu - lam - 2 * s := by
    have a1 : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt hmu.le
    have a2 : Real.sqrt (mu - lam) ^ 2 = mu - lam := Real.sq_sqrt hml'.le
    nlinarith
  have hpi : piFn mu cbar lam = cbar * (2 * mu - lam - 2 * s) / (mu * (mu - lam)) := by
    unfold piFn; rw [e5]; ring
  have hp : pFn mu cbar lam = (mu - s) * lam * cbar / ((mu - lam) * mu ^ 2) := by
    unfold pFn; rw [← hsdef]
  have hcs : cFn mu cbar lam = (s - (mu - lam)) * cbar / lam := by
    unfold cFn; rw [← hsdef]
  rw [hpi, hp, hcs]
  set Z := cbar * (mu - lam) + lam * c with hZ
  have hZlo : cbar * (mu - lam) ≤ Z := by nlinarith
  have hZhi : Z ≤ mu * cbar := by nlinarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (mul_pos hcb hml') hZlo
  set d := c - (s - (mu - lam)) * cbar / lam with hd
  have hdl : lam * d = Z - cbar * s := by
    rw [hd, hZ]; field_simp; ring
  -- E1: the revenue gap
  have E1 : cbar * (2 * mu - lam - 2 * s) / (mu * (mu - lam)) -
      c * lam ^ 2 * cbar / (mu * (mu - lam) * Z) * (1 - c / cbar) =
      (lam * d) ^ 2 / (mu * (mu - lam) * Z) := by
    rw [hdl]
    field_simp
    rw [hZ]
    linear_combination (-(cbar ^ 2)) * hs2
  -- E2: the price gap
  have E2 : c * lam ^ 2 * cbar / (mu * (mu - lam) * Z) - (mu - s) * lam * cbar / ((mu - lam) * mu ^ 2)
      = lam * cbar * (lam * d) / (mu * s * Z) := by
    rw [hdl]
    field_simp
    rw [hZ]
    linear_combination (c * lam - lam * cbar + mu * cbar) * hs2
  rw [E1, E2]
  constructor
  · rw [mul_pow, div_mul_eq_mul_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ lam ^ 2 * d ^ 2 * mu * (mu - lam) := by positivity
    nlinarith
  · have : (mu ^ 2 * (mu - lam) / (lam ^ 2 * cbar)) * (lam * cbar * (lam * d) / (mu * s * Z)) ^ 2
        = lam ^ 2 * cbar * d ^ 2 * (mu - lam) / (s ^ 2 * Z ^ 2) := by
      field_simp
    rw [this, hs2, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ lam ^ 2 * d ^ 2 * mu * (mu - lam) * Z := by positivity
    nlinarith


/-- `ψ(c) = c (W_R(c) − W_F(c))`. -/
noncomputable def psi (mu cbar lam c : ℝ) : ℝ := c * (WR mu cbar lam c - WF mu cbar lam c)

lemma revCut_eq (mu cbar lam c : ℝ) (hlam : 0 < lam) (hml : lam < mu) (hcb : 0 < cbar)
    (hc : 0 ≤ c) : revCut mu cbar lam c = psi mu cbar lam c * (1 - c / cbar) := by
  have hmu : 0 < mu := by linarith
  have hml' : 0 < mu - lam := by linarith
  unfold psi
  rw [psi_eq mu cbar lam c hlam hml hcb hc]
  have hZ : mu * cbar - (cbar - c) * lam = cbar * (mu - lam) + lam * c := by ring
  have hZ0 : 0 < cbar * (mu - lam) + lam * c := by
    have : 0 < cbar * (mu - lam) := mul_pos hcb hml'
    nlinarith
  unfold revCut
  rw [hZ]
  field_simp

/-- All single-rate facts used downstream. -/
lemma rate_facts (mu cbar lam : ℝ) (hlam : 0 < lam) (hml : lam < mu) (hcb : 0 < cbar) :
    psi mu cbar lam (cFn mu cbar lam) = pFn mu cbar lam ∧
    pFn mu cbar lam * (1 - cFn mu cbar lam / cbar) = piFn mu cbar lam ∧
    0 < piFn mu cbar lam ∧ 0 < cFn mu cbar lam ∧ cFn mu cbar lam < cbar ∧
    (∀ c, 0 ≤ c → c ≤ cbar → psi mu cbar lam c * (1 - c / cbar) ≤ piFn mu cbar lam) ∧
    (∀ c, 0 ≤ c → c ≤ cbar → psi mu cbar lam c * (1 - c / cbar) = piFn mu cbar lam →
      c = cFn mu cbar lam) := by
  obtain ⟨-, ⟨hc0, hc1⟩, -, hrev, hpsi⟩ :=
    AdvSellUpgrade.Online.prop3_cutoff_problem mu cbar lam hlam hml hcb
  have hmu : 0 < mu := by linarith
  have hml' : 0 < mu - lam := by linarith
  have hk : 0 < lam ^ 2 / (mu ^ 2 * (mu - lam) * cbar) := by positivity
  refine ⟨hpsi, ?_, ?_, hc0, hc1, ?_, ?_⟩
  · have e := revCut_eq mu cbar lam _ hlam hml hcb hc0.le
    rw [hrev] at e
    rw [e, ← hpsi]; rfl
  · unfold piFn
    have : Real.sqrt (mu - lam) < Real.sqrt mu := Real.sqrt_lt_sqrt hml'.le (by linarith)
    have : 0 < (Real.sqrt mu - Real.sqrt (mu - lam)) ^ 2 := by
      apply pow_pos; linarith
    positivity
  · intro c h0 h1
    have := (gap mu cbar lam c hlam hml hcb h0 h1).1
    unfold psi
    nlinarith [sq_nonneg (c - cFn mu cbar lam)]
  · intro c h0 h1 heq
    have := (gap mu cbar lam c hlam hml hcb h0 h1).1
    unfold psi at heq
    rw [heq, sub_self] at this
    have h2 : (c - cFn mu cbar lam) ^ 2 ≤ 0 := by
      by_contra hneg
      replace hneg := lt_of_not_ge hneg
      have := mul_pos hk hneg
      linarith
    have : c - cFn mu cbar lam = 0 := by nlinarith [sq_nonneg (c - cFn mu cbar lam)]
    linarith

/-- `p` is strictly increasing in the rate. -/
lemma p_mono (mu cbar l1 l2 : ℝ) (h1 : 0 < l1) (h12 : l1 < l2) (h2 : l2 < mu) (hcb : 0 < cbar) :
    pFn mu cbar l1 < pFn mu cbar l2 := by
  have hmu : 0 < mu := by linarith
  unfold pFn
  have hs1 : Real.sqrt (mu * (mu - l2)) < Real.sqrt (mu * (mu - l1)) :=
    Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
  have hs1' : Real.sqrt (mu * (mu - l1)) < mu := by
    rw [Real.sqrt_lt' hmu]; nlinarith
  have a1 : 0 < (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar := by
    have : 0 < mu - Real.sqrt (mu * (mu - l1)) := by linarith
    positivity
  have a12 : (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar <
      (mu - Real.sqrt (mu * (mu - l2))) * l2 * cbar := by
    have e : 0 < mu - Real.sqrt (mu * (mu - l1)) := by linarith
    have : (mu - Real.sqrt (mu * (mu - l1))) * l1 < (mu - Real.sqrt (mu * (mu - l2))) * l2 := by
      nlinarith
    exact mul_lt_mul_of_pos_right this hcb
  have b2 : 0 < (mu - l2) * mu ^ 2 := by
    have : 0 < mu - l2 := by linarith
    positivity
  have b12 : (mu - l2) * mu ^ 2 < (mu - l1) * mu ^ 2 := by
    have : 0 < mu ^ 2 := by positivity
    nlinarith
  calc (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar / ((mu - l1) * mu ^ 2)
      < (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar / ((mu - l2) * mu ^ 2) :=
        div_lt_div_of_pos_left a1 b2 b12
    _ < _ := div_lt_div_of_pos_right a12 b2

/-- Weighted sum of squares under a linear constraint. -/
lemma sos (A B u w δ : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (h : δ ≤ u + w) :
    A * B * δ ^ 2 / (A + B) ≤ A * u ^ 2 + B * w ^ 2 := by
  rw [div_le_iff₀ (by linarith)]
  have h1 : δ ^ 2 ≤ (u + w) ^ 2 := by nlinarith
  have h2 : A * B * (u + w) ^ 2 ≤ (A * u ^ 2 + B * w ^ 2) * (A + B) := by
    nlinarith [sq_nonneg (A * u - B * w)]
  have : 0 < A * B := mul_pos hA hB
  nlinarith


/-- Evaluation of the common objective form `Pa(1 − cf/c̄) + M(cf − cr)/c̄ + m cr/c̄` on the
constraints of (7)/(8). -/
lemma eval (P : Params) (hP : P.Standing) (cr cf Pa M : ℝ)
    (h2' : cr < cf → M - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr))
    (h3' : cf < P.cbar → Pa - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr)
        + (1 - P.alpha) * cf * (WR P.mu P.cbar P.lamL cf - WF P.mu P.cbar P.lamL cf))
    (h0 : 0 < cr) (hle : cr ≤ cf) (hcf : cf ≤ P.cbar) :
    (cf < P.cbar → Pa * (1 - cf / P.cbar) + M * ((cf - cr) / P.cbar) + min P.Ba P.Bs * (cr / P.cbar)
      = min P.Ba P.Bs + P.alpha * (psi P.mu P.cbar P.lamH cr * (1 - cr / P.cbar))
        + (1 - P.alpha) * (psi P.mu P.cbar P.lamL cf * (1 - cf / P.cbar))) ∧
    (cf = P.cbar → Pa * (1 - cf / P.cbar) + M * ((cf - cr) / P.cbar) + min P.Ba P.Bs * (cr / P.cbar)
      ≤ min P.Ba P.Bs + P.alpha * piFn P.mu P.cbar P.lamH) := by
  have h2 : cr < cf → M - min P.Ba P.Bs = P.alpha * psi P.mu P.cbar P.lamH cr := fun h => by
    rw [h2' h]; unfold psi; ring
  have h3 : cf < P.cbar → Pa - min P.Ba P.Bs =
      P.alpha * psi P.mu P.cbar P.lamH cr + (1 - P.alpha) * psi P.mu P.cbar P.lamL cf := fun h => by
    rw [h3' h]; unfold psi; ring
  obtain ⟨hl0, hlh, hhm, hcb, ha0, ha1⟩ := hP
  have Fh := rate_facts P.mu P.cbar P.lamH (by linarith) hhm hcb
  constructor
  · intro hlt
    have e3 := h3 hlt
    rcases lt_or_eq_of_le hle with h | h
    · have e2 := h2 h
      linear_combination (1 - cf / P.cbar) * e3 + ((cf - cr) / P.cbar) * e2
    · subst h
      linear_combination (1 - cr / P.cbar) * e3
  · intro heq
    subst heq
    have hz : (1 - P.cbar / P.cbar) = 0 := by field_simp; ring
    rcases lt_or_eq_of_le hle with h | h
    · have e2 := h2 h
      have hb := Fh.2.2.2.2.2.1 cr h0.le hle
      have : Pa * (1 - P.cbar / P.cbar) + M * ((P.cbar - cr) / P.cbar)
          + min P.Ba P.Bs * (cr / P.cbar)
          = min P.Ba P.Bs + P.alpha * (psi P.mu P.cbar P.lamH cr * (1 - cr / P.cbar)) := by
        rw [hz]
        have : M = min P.Ba P.Bs + P.alpha * psi P.mu P.cbar P.lamH cr := by linarith
        rw [this]; field_simp; ring
      rw [this]
      nlinarith
    · subst h
      have hpi := Fh.2.2.1
      rw [hz]
      have : (P.cbar - P.cbar) / P.cbar = 0 := by simp
      rw [this, div_self hcb.ne']
      nlinarith

/-- Upper bound `V` and identification of the maximisers. -/
lemma bound (P : Params) (hP : P.Standing) (cr cf Pa M : ℝ)
    (h2' : cr < cf → M - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr))
    (h3' : cf < P.cbar → Pa - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr)
        + (1 - P.alpha) * cf * (WR P.mu P.cbar P.lamL cf - WF P.mu P.cbar P.lamL cf))
    (h0 : 0 < cr) (hle : cr ≤ cf) (hcf : cf ≤ P.cbar) :
    Pa * (1 - cf / P.cbar) + M * ((cf - cr) / P.cbar) + min P.Ba P.Bs * (cr / P.cbar)
      ≤ P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
        + min P.Ba P.Bs ∧
    (Pa * (1 - cf / P.cbar) + M * ((cf - cr) / P.cbar) + min P.Ba P.Bs * (cr / P.cbar)
      = P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
        + min P.Ba P.Bs → cr = cFn P.mu P.cbar P.lamH ∧ cf = cFn P.mu P.cbar P.lamL) := by
  have E := eval P hP cr cf Pa M h2' h3' h0 hle hcf
  obtain ⟨hl0, hlh, hhm, hcb, ha0, ha1⟩ := hP
  have Fh := rate_facts P.mu P.cbar P.lamH (by linarith) hhm hcb
  have Fl := rate_facts P.mu P.cbar P.lamL hl0 (by linarith) hcb
  have hpl := Fl.2.2.1
  have hph := Fh.2.2.1
  rcases lt_or_eq_of_le hcf with h | h
  · rw [E.1 h]
    have bh := Fh.2.2.2.2.2.1 cr h0.le (by linarith)
    have bl := Fl.2.2.2.2.2.1 cf (by linarith) hcf
    refine ⟨by nlinarith, fun heq => ?_⟩
    have qh : psi P.mu P.cbar P.lamH cr * (1 - cr / P.cbar) = piFn P.mu P.cbar P.lamH := by
      nlinarith
    have ql : psi P.mu P.cbar P.lamL cf * (1 - cf / P.cbar) = piFn P.mu P.cbar P.lamL := by
      nlinarith
    exact ⟨Fh.2.2.2.2.2.2 cr h0.le (by linarith) qh, Fl.2.2.2.2.2.2 cf (by linarith) hcf ql⟩
  · have := E.2 h
    have : 0 < (1 - P.alpha) * piFn P.mu P.cbar P.lamL := mul_pos (by linarith) hpl
    refine ⟨by linarith, fun heq => ?_⟩
    exfalso; linarith


/-- A price vector with cutoffs `(c(λh), c(λl))` satisfying the two binding equations is optimal in (8). -/
lemma feas_point (P : Params) (hP : P.Standing) (Pa Ps K : ℝ)
    (hM : min (P.alpha * Ps + (1 - P.alpha) * P.Bs) (P.Ba + P.alpha * K)
      = min P.Ba P.Bs + P.alpha * pFn P.mu P.cbar P.lamH)
    (hPa : Pa = min P.Ba P.Bs + P.alpha * pFn P.mu P.cbar P.lamH
      + (1 - P.alpha) * pFn P.mu P.cbar P.lamL)
    (h1 : Pa ≤ Ps) (h2 : Pa ≤ P.Ba + K) :
    FeasAUS P (cFn P.mu P.cbar P.lamH) (cFn P.mu P.cbar P.lamL) Pa Ps K ∧
      objAUS P (cFn P.mu P.cbar P.lamH) (cFn P.mu P.cbar P.lamL) Pa Ps K =
        P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
          + min P.Ba P.Bs := by
  obtain ⟨c0, c01, c1⟩ := AdvSellUpgrade.Online.cutoff_order P hP
  have hP' := hP
  obtain ⟨hl0, hlh, hhm, hcb, ha0, ha1⟩ := hP'
  have Fh := rate_facts P.mu P.cbar P.lamH (by linarith) hhm hcb
  have Fl := rate_facts P.mu P.cbar P.lamL hl0 (by linarith) hcb
  have ph := Fh.1
  have pl := Fl.1
  unfold psi at ph pl
  have hfe : FeasAUS P (cFn P.mu P.cbar P.lamH) (cFn P.mu P.cbar P.lamL) Pa Ps K := by
    refine ⟨h1, h2, fun _ => ?_, fun _ => ?_, fun h => absurd h (ne_of_lt c1), c0, c01.le, c1.le⟩
    · rw [mul_assoc, ph, hM]; ring
    · rw [mul_assoc, mul_assoc, ph, pl, hPa]; ring
  refine ⟨hfe, ?_⟩
  have E := (eval P hP _ _ Pa _ hfe.2.2.1 hfe.2.2.2.1 c0 c01.le c1.le).1 c1
  unfold objAUS
  rw [E, Fh.1, Fl.1, Fh.2.1, Fl.2.1]
  ring

end Aux_ASUT1

open AdvSellUpgrade.Online Aux_ASUT1 in
theorem solution (P : Params) (hP : P.Standing) :
    let ph := pFn P.mu P.cbar P.lamH
    let pl := pFn P.mu P.cbar P.lamL
    let ch := cFn P.mu P.cbar P.lamH
    let cl := cFn P.mu P.cbar P.lamL
    let V := P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
      + min P.Ba P.Bs
    IsGreatest (ausValues P) V ∧
    (∀ cr cf Pa Ps K, FeasAUS P cr cf Pa Ps K → objAUS P cr cf Pa Ps K = V →
      cr = ch ∧ cf = cl) ∧
    (P.Bs - P.Ba < 0 →
      ∀ K, max 0 (max ((P.Bs - P.Ba) / P.alpha + ph)
          (P.Bs - P.Ba + P.alpha * ph + (1 - P.alpha) * pl)) ≤ K →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Bs) (ph + P.Bs) K ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Bs) (ph + P.Bs) K = V) ∧
    (0 ≤ P.Bs - P.Ba → P.Bs - P.Ba < P.alpha * (ph - pl) →
      (∀ K, ph ≤ K →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba)
            (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) K ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba)
            (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) K = V) ∧
      (∀ Ps, ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha ≤ Ps →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph = V)) ∧
    (P.alpha * (ph - pl) ≤ P.Bs - P.Ba →
      ∀ Ps, P.alpha * ph + (1 - P.alpha) * pl + P.Ba ≤ Ps →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph = V) := by
  intro ph pl ch cl V
  have hP' := hP
  obtain ⟨hl0, hlh, hhm, hcb, ha0, ha1⟩ := hP'
  have hmono : pl < ph := p_mono P.mu P.cbar P.lamL P.lamH hl0 hlh hhm hcb
  have hαinv : P.alpha * (1 / P.alpha) = 1 := by field_simp
  -- part 3
  have part3 : P.Bs - P.Ba < 0 →
      ∀ K, max 0 (max ((P.Bs - P.Ba) / P.alpha + ph)
          (P.Bs - P.Ba + P.alpha * ph + (1 - P.alpha) * pl)) ≤ K →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Bs) (ph + P.Bs) K ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Bs) (ph + P.Bs) K = V := by
    intro hneg K hK
    have hm : min P.Ba P.Bs = P.Bs := min_eq_right (by linarith)
    have k2 : (P.Bs - P.Ba) / P.alpha + ph ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hK)
    have k3 : P.Bs - P.Ba + P.alpha * ph + (1 - P.alpha) * pl ≤ K :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hK)
    have k2' : P.Bs - P.Ba + P.alpha * ph ≤ P.alpha * K := by
      have := mul_le_mul_of_nonneg_left k2 ha0.le
      have e : P.alpha * ((P.Bs - P.Ba) / P.alpha + ph) = P.Bs - P.Ba + P.alpha * ph := by
        field_simp
      linarith
    apply feas_point P hP
    · rw [hm, min_eq_left (by linarith)]; ring
    · rw [hm]; ring
    · nlinarith
    · linarith
  -- part 4
  have part4 : 0 ≤ P.Bs - P.Ba → P.Bs - P.Ba < P.alpha * (ph - pl) →
      (∀ K, ph ≤ K →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba)
            (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) K ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba)
            (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) K = V) ∧
      (∀ Ps, ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha ≤ Ps →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph = V) := by
    intro h0 h1
    have hm : min P.Ba P.Bs = P.Ba := min_eq_left (by linarith)
    have e : P.alpha * (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) + (1 - P.alpha) * P.Bs
        = P.Ba + P.alpha * ph := by field_simp; ring
    -- Pa ≤ the threshold spot price
    have hle : P.alpha * ph + (1 - P.alpha) * pl + P.Ba ≤ ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha := by
      have : P.alpha * (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) ≤
          P.alpha * (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) := by
        have e2 : P.alpha * (ph + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha)
            = P.alpha * ph + P.Ba - (1 - P.alpha) * P.Bs := by field_simp; ring
        rw [e2]
        nlinarith
      exact le_of_mul_le_mul_left this ha0
    refine ⟨fun K hK => ?_, fun Ps hPs => ?_⟩
    · apply feas_point P hP
      · rw [hm, e, min_eq_left (by nlinarith)]
      · rw [hm]; ring
      · exact hle
      · nlinarith
    · apply feas_point P hP
      · rw [hm, min_eq_right]
        have := mul_le_mul_of_nonneg_left hPs ha0.le
        linarith
      · rw [hm]; ring
      · linarith
      · nlinarith
  -- part 5
  have part5 : P.alpha * (ph - pl) ≤ P.Bs - P.Ba →
      ∀ Ps, P.alpha * ph + (1 - P.alpha) * pl + P.Ba ≤ Ps →
        FeasAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph ∧
          objAUS P ch cl (P.alpha * ph + (1 - P.alpha) * pl + P.Ba) Ps ph = V := by
    intro h Ps hPs
    have hba : 0 ≤ P.Bs - P.Ba := le_trans (mul_nonneg ha0.le (by linarith)) h
    have hm : min P.Ba P.Bs = P.Ba := min_eq_left (by linarith)
    apply feas_point P hP
    · rw [hm, min_eq_right]
      have := mul_le_mul_of_nonneg_left hPs ha0.le
      nlinarith
    · rw [hm]; ring
    · exact hPs
    · nlinarith
  -- upper bound and uniqueness
  have hub : ∀ cr cf Pa Ps K, FeasAUS P cr cf Pa Ps K →
      objAUS P cr cf Pa Ps K ≤ V ∧ (objAUS P cr cf Pa Ps K = V → cr = ch ∧ cf = cl) := by
    intro cr cf Pa Ps K hf
    obtain ⟨-, -, f2, f3, -, f5, f6, f7⟩ := hf
    exact bound P hP cr cf Pa _ f2 f3 f5 f6 f7
  refine ⟨⟨?_, ?_⟩, fun cr cf Pa Ps K hf he => (hub cr cf Pa Ps K hf).2 he, part3, part4, part5⟩
  · rcases lt_or_ge (P.Bs - P.Ba) 0 with h | h
    · have := part3 h _ le_rfl
      exact ⟨_, _, _, _, _, this.1, this.2.symm⟩
    · rcases lt_or_ge (P.Bs - P.Ba) (P.alpha * (ph - pl)) with h' | h'
      · have := (part4 h h').1 ph le_rfl
        exact ⟨_, _, _, _, _, this.1, this.2.symm⟩
      · have := part5 h' _ le_rfl
        exact ⟨_, _, _, _, _, this.1, this.2.symm⟩
  · rintro v ⟨cr, cf, Pa, Ps, K, hf, rfl⟩
    exact (hub cr cf Pa Ps K hf).1
