-- Prove2me | Definitions.Def_LotteryInterm_IID_Intermediary
-- name    : LotteryInterm_IID_Intermediary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:33.49864+00:00
-- url     : https://prove2.me/theorems/f4bee61a-eec4-401d-9314-d9804b60dcad
-- title:
--   Intermediary best responses and worst-case seller revenue
-- statement:
--   For a seller menu $M$, bidders value intermediary access at $u_M(v_i)$ while continuing to report original values. A best response is an admissible BIC/IR mechanism attaining the defined optimum $\operatorname{OptRev}(F,u_M)$; optimality is not assumed as a field of a mechanism.
--
--   If $\operatorname{pay}_M(v_i)$ is the selected menu payment, the seller receives
--   $$\operatorname{SelRev}(M,I)=\mathbb E\!\left[\sum_i y_i(v)\operatorname{pay}_M(v_i)\right].$$
--   Define $\operatorname{RandMI}(M)$ as the infimum of these revenues over all intermediary best responses, and set it to $-\infty$ when no best response exists. Finally $\operatorname{DET}=\sup_{p\ge0}\operatorname{RandMI}(\{(1,p)\})$.
--
--   Finite menus bound seller payments. Together with measurable feasible allocations, this makes seller revenue integrable. The infimum includes every best response, extending the source's Assumption 3.2 and preventing a seller-favourable choice of intermediary.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §2.1–2.2, pp.7–9 (PDF pp.8–10); §3.1 and Assumptions 3.2–3.3, pp.9–10 (PDF pp.10–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Mechanism
import Definitions.Def_LotteryInterm_IID_Menu

open MeasureTheory

namespace LotteryInterm.IID

def BestResponse {n : ℕ} (D : Fin n → ValueDist) (M : Menu) (I : Mechanism n) : Prop :=
  Admissible D (accessUtility M) I ∧
    (revenue (prior D) I : EReal) = OptRev D (accessUtility M)

noncomputable def sellerRevenue {n : ℕ} (D : Fin n → ValueDist) (M : Menu)
    (I : Mechanism n) : ℝ :=
  ∫ v, ∑ i, I.allocation v i * menuPayment M (v i) ∂prior D

/-- Infimum over every best response. Failure of existence is a loss, not a vacuous
positive guarantee. Finite menus bound their payments, so these integrals are integrable
for every admissible allocation. -/
noncomputable def RandMI {n : ℕ} (D : Fin n → ValueDist) (M : Menu) : EReal :=
  by
  classical
  exact if ∃ I, BestResponse D M I then
    sInf {r | ∃ I, BestResponse D M I ∧ (sellerRevenue D M I : EReal) = r}
  else ⊥

noncomputable def DET {n : ℕ} (D : Fin n → ValueDist) : EReal :=
  ⨆ (p : ℝ) (hp : 0 ≤ p), RandMI D (postedPrice p hp)

end LotteryInterm.IID


