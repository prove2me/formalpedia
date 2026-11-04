-- Prove2me | solution 1 for AdvSellUpgrade.Online.proposition_5_gap
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:52:21.299857+00:00
-- url     : https://prove2.me/submissions/571d609e-40c7-436a-9e65-8695ae57ec0a

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
theorem solution (P : Params) (hP : P.Standing)
    (hgap : P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) < P.Bs - P.Ba) :
    ∃ v : ℝ, v < P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL + P.Ba ∧
      ∀ cr cf Pa Ps, FeasAS P cr cf Pa Ps → objAS P cr cf Pa Ps ≤ v := by
  obtain ⟨c0, c01, c1⟩ := cutoff_order P hP
  have hP' := hP
  obtain ⟨hl0, hlh, hhm, hcb, ha0, ha1⟩ := hP'
  have hmono := p_mono P.mu P.cbar P.lamL P.lamH hl0 hlh hhm hcb
  have Fh := rate_facts P.mu P.cbar P.lamH (by linarith) hhm hcb
  have Fl := rate_facts P.mu P.cbar P.lamL hl0 (by linarith) hcb
  have hBa : P.Ba < P.Bs := by nlinarith
  have hm : min P.Ba P.Bs = P.Ba := min_eq_left hBa.le
  have hμh : 0 < P.mu - P.lamH := by linarith
  have hμl : 0 < P.mu - P.lamL := by linarith
  have hmu : 0 < P.mu := by linarith
  have hlH : 0 < P.lamH := by linarith
  have h1a : 0 < 1 - P.alpha := by linarith
  obtain ⟨k2h, hk2h⟩ : ∃ k, k = P.mu ^ 2 * (P.mu - P.lamH) / (P.lamH ^ 2 * P.cbar) := ⟨_, rfl⟩
  obtain ⟨k2l, hk2l⟩ : ∃ k, k = P.mu ^ 2 * (P.mu - P.lamL) / (P.lamL ^ 2 * P.cbar) := ⟨_, rfl⟩
  obtain ⟨k1h, hk1h⟩ : ∃ k, k = P.lamH ^ 2 / (P.mu ^ 2 * (P.mu - P.lamH) * P.cbar) := ⟨_, rfl⟩
  obtain ⟨k1l, hk1l⟩ : ∃ k, k = P.lamL ^ 2 / (P.mu ^ 2 * (P.mu - P.lamL) * P.cbar) := ⟨_, rfl⟩
  have hk2h0 : 0 < k2h := by rw [hk2h]; positivity
  have hk2l0 : 0 < k2l := by rw [hk2l]; positivity
  have hk1h0 : 0 < k1h := by rw [hk1h]; positivity
  have hk1l0 : 0 < k1l := by rw [hk1l]; positivity
  have hA0 : 0 < P.alpha * k2h := mul_pos ha0 hk2h0
  have hB0 : 0 < (1 - P.alpha) * k2l := mul_pos h1a hk2l0
  have hA'0 : 0 < P.alpha * k1h := mul_pos ha0 hk1h0
  have hB'0 : 0 < (1 - P.alpha) * k1l := mul_pos h1a hk1l0
  obtain ⟨δ, hδ⟩ : ∃ d, d = (P.Bs - P.Ba) / P.alpha
      - (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) := ⟨_, rfl⟩
  have hαδ : P.alpha * δ = P.Bs - P.Ba
      - P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) := by
    rw [hδ]; field_simp
  have hδ0 : 0 < δ := by
    by_contra hn
    have : P.alpha * δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0.le (le_of_not_gt hn)
    linarith
  obtain ⟨ε1, hε1d⟩ : ∃ e, e = (P.alpha * k2h) * ((1 - P.alpha) * k2l) * δ ^ 2
      / (P.alpha * k2h + (1 - P.alpha) * k2l) := ⟨_, rfl⟩
  obtain ⟨ε2, hε2d⟩ : ∃ e, e = (P.alpha * k1h) * ((1 - P.alpha) * k1l)
      * (cFn P.mu P.cbar P.lamL - cFn P.mu P.cbar P.lamH) ^ 2
      / (P.alpha * k1h + (1 - P.alpha) * k1l) := ⟨_, rfl⟩
  obtain ⟨ε3, hε3d⟩ : ∃ e, e = (1 - P.alpha) * piFn P.mu P.cbar P.lamL := ⟨_, rfl⟩
  have hε1 : 0 < ε1 := by rw [hε1d]; positivity
  have hε2 : 0 < ε2 := by
    have : 0 < cFn P.mu P.cbar P.lamL - cFn P.mu P.cbar P.lamH := by linarith
    rw [hε2d]; positivity
  have hε3 : 0 < ε3 := by rw [hε3d]; exact mul_pos h1a Fl.2.2.1
  obtain ⟨ε, hε⟩ : ∃ e, e = min ε1 (min ε2 ε3) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min hε1 (lt_min hε2 hε3)
  have hεε1 : ε ≤ ε1 := by rw [hε]; exact min_le_left _ _
  have hεε2 : ε ≤ ε2 := by rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεε3 : ε ≤ ε3 := by rw [hε]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL + P.Ba - ε,
    by linarith, ?_⟩
  intro cr cf Pa Ps hf
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  have E := eval P hP cr cf Pa _ f2 f3 f5 f6 f7
  rw [hm] at E
  have hobj : objAS P cr cf Pa Ps = Pa * (1 - cf / P.cbar)
      + (P.alpha * Ps + (1 - P.alpha) * P.Bs) * ((cf - cr) / P.cbar) + P.Ba * (cr / P.cbar) := by
    unfold objAS; rw [hm]
  rw [hobj]
  rcases lt_or_eq_of_le f7 with hcf | hcf
  · rw [E.1 hcf]
    have gh := gap P.mu P.cbar P.lamH cr hlH hhm hcb f5.le (by linarith)
    have gl := gap P.mu P.cbar P.lamL cf hl0 (by linarith) hcb (by linarith) f7
    rw [← hk1h, ← hk2h] at gh
    rw [← hk1l, ← hk2l] at gl
    rcases lt_or_eq_of_le f6 with hlt | heq
    · -- two distinct cutoffs: the price constraint Pa ≤ Ps separates the price gaps
      have e2 := f2 hlt
      have e3 := f3 hcf
      rw [hm] at e2 e3
      have e2' : P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba
          = P.alpha * psi P.mu P.cbar P.lamH cr := by rw [e2]; unfold psi; ring
      have e3' : Pa - P.Ba = P.alpha * psi P.mu P.cbar P.lamH cr
          + (1 - P.alpha) * psi P.mu P.cbar P.lamL cf := by rw [e3]; unfold psi; ring
      have key : (1 - P.alpha) * ((P.Bs - P.Ba) - P.alpha * (psi P.mu P.cbar P.lamH cr
          - psi P.mu P.cbar P.lamL cf)) ≤ 0 := by
        have := mul_le_mul_of_nonneg_left f1 ha0.le
        linear_combination this - P.alpha * e3' + e2'
      have key2 : (P.Bs - P.Ba) - P.alpha * (psi P.mu P.cbar P.lamH cr
          - psi P.mu P.cbar P.lamL cf) ≤ 0 := by
        by_contra hn
        have := mul_pos h1a (lt_of_not_ge hn)
        linarith
      have huw : δ ≤ (psi P.mu P.cbar P.lamH cr - pFn P.mu P.cbar P.lamH)
          + (pFn P.mu P.cbar P.lamL - psi P.mu P.cbar P.lamL cf) := by
        by_contra hn
        have h' := lt_of_not_ge hn
        have := mul_lt_mul_of_pos_left h' ha0
        linarith
      have hs := sos _ _ _ _ δ hA0 hB0 hδ0 huw
      rw [← hε1d] at hs
      have g1 : k2h * (psi P.mu P.cbar P.lamH cr - pFn P.mu P.cbar P.lamH) ^ 2
          ≤ piFn P.mu P.cbar P.lamH - psi P.mu P.cbar P.lamH cr * (1 - cr / P.cbar) := gh.2
      have g2 : k2l * (psi P.mu P.cbar P.lamL cf - pFn P.mu P.cbar P.lamL) ^ 2
          ≤ piFn P.mu P.cbar P.lamL - psi P.mu P.cbar P.lamL cf * (1 - cf / P.cbar) := gl.2
      have hsq : (pFn P.mu P.cbar P.lamL - psi P.mu P.cbar P.lamL cf) ^ 2
          = (psi P.mu P.cbar P.lamL cf - pFn P.mu P.cbar P.lamL) ^ 2 := by ring
      rw [hsq] at hs
      have m1 := mul_le_mul_of_nonneg_left g1 ha0.le
      have m2 := mul_le_mul_of_nonneg_left g2 h1a.le
      linarith
    · -- equal cutoffs
      subst heq
      have g1 : k1h * (cr - cFn P.mu P.cbar P.lamH) ^ 2
          ≤ piFn P.mu P.cbar P.lamH - psi P.mu P.cbar P.lamH cr * (1 - cr / P.cbar) := gh.1
      have g2 : k1l * (cr - cFn P.mu P.cbar P.lamL) ^ 2
          ≤ piFn P.mu P.cbar P.lamL - psi P.mu P.cbar P.lamL cr * (1 - cr / P.cbar) := gl.1
      have hs := sos _ _ (cr - cFn P.mu P.cbar P.lamH) (cFn P.mu P.cbar P.lamL - cr)
        (cFn P.mu P.cbar P.lamL - cFn P.mu P.cbar P.lamH) hA'0 hB'0 (by linarith) (by linarith)
      rw [← hε2d] at hs
      have hsq : (cFn P.mu P.cbar P.lamL - cr) ^ 2 = (cr - cFn P.mu P.cbar P.lamL) ^ 2 := by ring
      rw [hsq] at hs
      have m1 := mul_le_mul_of_nonneg_left g1 ha0.le
      have m2 := mul_le_mul_of_nonneg_left g2 h1a.le
      linarith
  · have := E.2 hcf
    rw [hε3d] at hεε3
    linarith
