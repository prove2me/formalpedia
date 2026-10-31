-- Prove2me | Definitions.Def_AdvanceSellDistress_ClosedForms
-- name    : AdvanceSellDistress_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:25.091172+00:00
-- url     : https://prove2.me/theorems/ed664b6c-ccb4-4ade-92af-f4009785ff4e
-- title:
--   Closed-form values of Proposition 1, Lemma A.5 and Proposition 10
-- statement:
--   The explicit values printed in the paper, used only as the right-hand sides of statements:
--
--   1. Proposition 1: $r^*_{FB}=1/\beta-1$, $e^*_{FB}=(1-\lambda)v_m/(2a)$, $\pi^*_{FB}=\beta[(1-\lambda)^2v_m^2/(4a)+\lambda v_m]-I$, and with $\Delta_B=(1-\lambda)^2v_m^2-8a(I/\beta-\lambda v_m)$,
--   $$r^*_B=\frac{(1+\lambda)v_m-\sqrt{\Delta_B}}{2I}-1,\qquad e^*_B=\frac{(1-\lambda)v_m+\sqrt{\Delta_B}}{4a},\qquad \pi^*_B=\beta a(e^*_B)^2 .$$
--   2. Lemma A.5: $p^h_{bb}(p_s)=I-\beta\lambda(p_s+m_o)$, $p^l_{bb}(p_s)=I-\beta[\lambda(p_s+m_o)+(1-\lambda)^2(p_s+m_o)^2/(8a)]$, $e^h_{bb}(p_s)=(1-\lambda)(p_s+m_o)/(2a)$, $\pi^h_{bb}(p_a,p_s)=\beta[(1-\lambda)^2(p_s+m_o)^2/(4a)+\lambda(p_s+m_o)]+p_a-I$, and with $\Delta_L=(1-\lambda)^2(p_s+m_o)^2-8a[(I-p_a)/\beta-\lambda(p_s+m_o)]$,
--   $$e^l_{bb}=\frac{(1-\lambda)(p_s+m_o)+\sqrt{\Delta_L}}{4a},\qquad r^l_{bb}=\frac{(1+\lambda)(p_s+m_o)-\sqrt{\Delta_L}}{2(I-p_a)}-1 .$$
--   3. Proposition 10 ($m_o=1$): $R=(1-\lambda)^2-2a(I/\beta-2\lambda)$,
--   $$\underline w^l_H=1+\frac{2\sqrt R}{1-\lambda},\qquad I_m=\beta\Big[2\lambda+\frac{3(1-\lambda)^2}{8a}\Big],\qquad p^u_s=\frac{\sqrt R}{1-\lambda},$$
--   $$p^{l*}_{sH}=v-1-\frac{\sqrt R}{1-\lambda},\quad p^{l*}_{aH}=I-\beta\lambda(p^{l*}_{sH}+1),\quad e^{l*}_H=\frac{(1-\lambda)(p^{l*}_{sH}+1)}{2a},\quad \pi^{l*}_H=\beta a(e^{l*}_H)^2 .$$
--
--   These are values, not definitions of the model's effort, interest rate, consumer decision or firm choice: those are the relations of `AdvanceSellDistress.Model`, and the theorems prove that the relations take these values.
--
--   **Formalization Note** Lean's `Real.sqrt` returns $0$ on negative input. Each statement that uses these values carries hypotheses (such as $I\le I_h$) that make the radicands nonnegative. $p^u_s$ is the spot price at which $e^h_{bb}(p_s)=e^*_B$ in Step 1 of the proof of Proposition A.7, at $m_o=1$.
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, Proposition 1 p.8 (PDF 9); Lemma A.5 pp.32–33 (PDF 33–34); Proposition 10 and the definitions before it, p.21 (PDF 22); proof of Proposition A.7 Step 1, p.79 (PDF 80)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model

namespace AdvanceSellDistress

namespace Params

variable (P : Params)

/-! These are the closed-form values printed in Papanastasiou–Xiao–Yang, *Advance Selling to Ease
Financial Distress*, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904. They are used
only as the values in statements; the model's effort, face value, consumer decision and firm
choice are the relations of `Def_AdvanceSellDistress_Model`.

**Formalization Note.** `Real.sqrt` of a negative number is `0` in Lean; every statement using these
values carries hypotheses that make the radicands nonnegative (e.g. `I ≤ I_h`). -/

/-- First-best interest rate `r*_FB = 1/β − 1`, Proposition 1(i), p. 8 (PDF 9). -/
noncomputable def rFB : ℝ := 1 / P.β - 1

/-- First-best effort `e*_FB = (1 − λ) v_m / (2a)`, Proposition 1(i), p. 8 (PDF 9). -/
noncomputable def eFB : ℝ := (1 - P.lam) * P.vm / (2 * P.a)

/-- First-best profit `π*_FB = β[(1 − λ)² v_m² / (4a) + λ v_m] − I`, Proposition 1(i), p. 8 (PDF 9). -/
noncomputable def piFB : ℝ :=
  P.β * ((1 - P.lam) ^ 2 * P.vm ^ 2 / (4 * P.a) + P.lam * P.vm) - P.I

/-- The radicand `(1 − λ)² v_m² − 8a (I/β − λ v_m)` of Proposition 1(ii), p. 8 (PDF 9). -/
noncomputable def radB : ℝ := (1 - P.lam) ^ 2 * P.vm ^ 2 - 8 * P.a * (P.I / P.β - P.lam * P.vm)

/-- `r*_B = [(1 + λ) v_m − √((1 − λ)² v_m² − 8a (I/β − λ v_m))] / (2I) − 1`, Proposition 1(ii), eq. (7),
pp. 8, 35 (PDF 9, 36). -/
noncomputable def rB : ℝ := ((1 + P.lam) * P.vm - Real.sqrt P.radB) / (2 * P.I) - 1

/-- `e*_B = [(1 − λ) v_m + √((1 − λ)² v_m² − 8a (I/β − λ v_m))] / (4a)`, Proposition 1(ii), p. 8 (PDF 9). -/
noncomputable def eB : ℝ := ((1 - P.lam) * P.vm + Real.sqrt P.radB) / (4 * P.a)

/-- `π*_B = β a (e*_B)²`, Proposition 1(ii), p. 8 (PDF 9). -/
noncomputable def piB : ℝ := P.β * P.a * P.eB ^ 2

/-- `p^h_bb(p_s) = I − β λ (p_s + m_o)`, Lemma A.5, p. 32 (PDF 33). -/
noncomputable def ph_bb (ps : ℝ) : ℝ := P.I - P.β * P.lam * (ps + P.mo)

/-- `p^l_bb(p_s) = I − β [λ (p_s + m_o) + (1 − λ)² (p_s + m_o)² / (8a)]`, Lemma A.5, p. 32 (PDF 33). -/
noncomputable def pl_bb (ps : ℝ) : ℝ :=
  P.I - P.β * (P.lam * (ps + P.mo) + (1 - P.lam) ^ 2 * (ps + P.mo) ^ 2 / (8 * P.a))

/-- `e^h_bb(p_s) = (1 − λ)(p_s + m_o) / (2a)`, Lemma A.5(1), p. 32 (PDF 33). -/
noncomputable def eh_bb (ps : ℝ) : ℝ := (1 - P.lam) * (ps + P.mo) / (2 * P.a)

/-- `π^h_bb(p_a, p_s) = β [(1 − λ)² (p_s + m_o)² / (4a) + λ (p_s + m_o)] + p_a − I`, Lemma A.5(1),
p. 32 (PDF 33). -/
noncomputable def pih_bb (pa ps : ℝ) : ℝ :=
  P.β * ((1 - P.lam) ^ 2 * (ps + P.mo) ^ 2 / (4 * P.a) + P.lam * (ps + P.mo)) + pa - P.I

/-- The radicand `(1 − λ)² (p_s + m_o)² − 8a [(I − p_a)/β − λ (p_s + m_o)]` of Lemma A.5(2), p. 33
(PDF 34). -/
noncomputable def radL (pa ps : ℝ) : ℝ :=
  (1 - P.lam) ^ 2 * (ps + P.mo) ^ 2 - 8 * P.a * ((P.I - pa) / P.β - P.lam * (ps + P.mo))

/-- `e^l_bb(p_a, p_s) = [(1 − λ)(p_s + m_o) + √(radL)] / (4a)`, Lemma A.5(2), p. 33 (PDF 34). -/
noncomputable def el_bb (pa ps : ℝ) : ℝ :=
  ((1 - P.lam) * (ps + P.mo) + Real.sqrt (P.radL pa ps)) / (4 * P.a)

/-- `r^l_bb(p_a, p_s) = [(1 + λ)(p_s + m_o) − √(radL)] / (2 (I − p_a)) − 1`, Lemma A.5(2), p. 33
(PDF 34). -/
noncomputable def rl_bb (pa ps : ℝ) : ℝ :=
  ((1 + P.lam) * (ps + P.mo) - Real.sqrt (P.radL pa ps)) / (2 * (P.I - pa)) - 1

/-- The radicand `R = (1 − λ)² − 2a (I/β − 2λ)` of `w^l_H` and `p^{l*}_{sH}` (Proposition 10, p. 21,
PDF 22; `m_o = 1`). -/
noncomputable def R : ℝ := (1 - P.lam) ^ 2 - 2 * P.a * (P.I / P.β - 2 * P.lam)

/-- The valuation threshold `w^l_H = 1 + 2 √R / (1 − λ)` (underlined in the paper), p. 21 (PDF 22). -/
noncomputable def wH : ℝ := 1 + 2 * Real.sqrt P.R / (1 - P.lam)

/-- `I_m = β [2λ + 3 (1 − λ)² / (8a)]`, p. 21 (PDF 22). -/
noncomputable def Im : ℝ := P.β * (2 * P.lam + 3 * (1 - P.lam) ^ 2 / (8 * P.a))

/-- `p^u_s = √R / (1 − λ)`, the spot price at which `e^h_bb(p_s) = e*_B` (proof of Proposition A.7,
Step 1, p. 79, PDF 80, at `m_o = 1`). -/
noncomputable def pu : ℝ := Real.sqrt P.R / (1 - P.lam)

/-- `p^{l*}_{sH} = v − 1 − √R / (1 − λ)`, Proposition 10(i), p. 21 (PDF 22). -/
noncomputable def psH : ℝ := P.v - 1 - Real.sqrt P.R / (1 - P.lam)

/-- `p^{l*}_{aH} = I − β λ (p^{l*}_{sH} + 1)`, Proposition 10(i), p. 21 (PDF 22). -/
noncomputable def paH : ℝ := P.I - P.β * P.lam * (P.psH + 1)

/-- `e^{l*}_H = (1 − λ)(p^{l*}_{sH} + 1) / (2a)`, Proposition 10(i), p. 21 (PDF 22). -/
noncomputable def eH : ℝ := (1 - P.lam) * (P.psH + 1) / (2 * P.a)

/-- `π^{l*}_H = β a (e^{l*}_H)²`, Proposition 10(i), p. 21 (PDF 22). -/
noncomputable def piH : ℝ := P.β * P.a * P.eH ^ 2

end Params

end AdvanceSellDistress


