-- Prove2me | Definitions.Def_LotteryInterm_IID_Supplement_MessageDependent
-- name    : LotteryInterm_IID_Supplement_MessageDependent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:32.284784+00:00
-- url     : https://prove2.me/theorems/1af33a30-b9d2-4a52-8352-e234c7b161c1
-- title:
--   The message-dependent intermediary model and $\mathrm{RandMD}$
-- statement:
--   In the **message-dependent model** (§2.1) the intermediary's auction may depend on the menu option a bidder asks for. By the revelation principle it is a direct mechanism: for each report profile $v$ and bidder $i$ it specifies the probability $y_i(v)\ge0$ that $i$ is forwarded, with $\sum_i y_i(v)\le1$; the probability $X_i(v)$ that $i$ receives the item and expected payment $P_i(v)$ to the seller, with
--   $$(X_i(v),P_i(v))=y_i(v)\,o\quad\text{for some } o\in\operatorname{conv}\mathcal O ,$$
--   so the forwarded option may be a lottery over menu options; and an expected fee $q_i(v)$ to the intermediary. Bidder $i$ of type $t$ reporting $t'$ has interim utility $\bar X_i(t')\,t-\bar P_i(t')-\bar q_i(t')$. Admissibility requires measurability, integrability, Bayesian incentive compatibility and interim individual rationality.
--
--   A **best response** is an admissible mechanism maximizing the expected fee revenue $\mathbb E[\sum_i q_i]$. The seller's revenue from it is $\mathbb E[\sum_i P_i]$, and
--   $$\mathrm{RandMD}(\mathcal O)=\inf\{\text{seller revenue of a best response}\},$$
--   with value $-\infty$ when no best response exists, the convention of the published $\mathrm{RandMI}$ (ties against the seller, Assumption 3.2).
--
--   These definitions are used by Theorem 5.1.
--
--   **Formalization Note** Per-bidder pairs in $y_i\cdot\operatorname{conv}\mathcal O$ represent the forwarding lotteries: the mean of a lottery over options lies in the convex hull of the options, and every hull point is the mean of a finite lottery.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §2.1, pp.7–8 (PDF pp.8–9); §5, Lemma 5.2 and its proof, pp.15–16 (PDF pp.16–17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_GeneralMenu

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- A direct mechanism of the intermediary in the message-dependent model (§2.1).
For a report profile `v` and bidder `i`: `selection v i` is the probability that `i`
is forwarded; `allocation v i` and `sellerPayment v i` are `i`'s probability of
receiving the item and expected payment to the seller, through the menu option the
intermediary forwards (which may depend on the reports); `fee v i` is `i`'s expected
payment to the intermediary. -/
structure MDMechanism (n : ℕ) where
  selection : (Fin n → ℝ) → Fin n → ℝ
  allocation : (Fin n → ℝ) → Fin n → ℝ
  sellerPayment : (Fin n → ℝ) → Fin n → ℝ
  fee : (Fin n → ℝ) → Fin n → ℝ

/-- At most one bidder is forwarded, and the forwarded bidder's (allocation, seller
payment) is the selection probability times a lottery over menu options: a point of
the convex hull of the options (randomization over options is allowed). -/
def MDFeasible {n : ℕ} (O : GenMenu) (M : MDMechanism n) : Prop :=
  (∀ v i, 0 ≤ M.selection v i) ∧
  (∀ v, (∑ i, M.selection v i) ≤ 1) ∧
  (∀ v i, ∃ o ∈ convexHull ℝ O.options,
    M.allocation v i = M.selection v i * o.1 ∧ M.sellerPayment v i = M.selection v i * o.2)

def MDWellDefined {n : ℕ} (μ : Measure (Fin n → ℝ)) (M : MDMechanism n) : Prop :=
  (∀ i, Measurable (fun v => M.selection v i)) ∧
  (∀ i, Measurable (fun v => M.allocation v i)) ∧
  (∀ i, Measurable (fun v => M.sellerPayment v i)) ∧
  (∀ i, Measurable (fun v => M.fee v i)) ∧
  (∀ i, Integrable (fun v => M.allocation v i) μ) ∧
  (∀ i, Integrable (fun v => M.sellerPayment v i) μ) ∧
  (∀ i, Integrable (fun v => M.fee v i) μ) ∧
  (∀ i t, Integrable (fun v => M.allocation (Function.update v i t) i) μ) ∧
  (∀ i t, Integrable (fun v => M.sellerPayment (Function.update v i t) i) μ) ∧
  (∀ i t, Integrable (fun v => M.fee (Function.update v i t) i) μ)

/-- Interim utility of bidder `i` with true value `t` who reports `report`. -/
noncomputable def mdInterimUtility {n : ℕ} (μ : Measure (Fin n → ℝ)) (M : MDMechanism n)
    (i : Fin n) (report t : ℝ) : ℝ :=
  (∫ v, M.allocation (Function.update v i report) i ∂μ) * t
    - (∫ v, M.sellerPayment (Function.update v i report) i ∂μ)
    - (∫ v, M.fee (Function.update v i report) i ∂μ)

def MDBIC {n : ℕ} (D : Fin n → ValueDist) (M : MDMechanism n) : Prop :=
  ∀ i, ∀ᵐ t ∂(D i).law, ∀ report : ℝ,
    mdInterimUtility (prior D) M i report t ≤ mdInterimUtility (prior D) M i t t

def MDInterimIR {n : ℕ} (D : Fin n → ValueDist) (M : MDMechanism n) : Prop :=
  ∀ i, ∀ᵐ t ∂(D i).law, 0 ≤ mdInterimUtility (prior D) M i t t

def MDAdmissible {n : ℕ} (D : Fin n → ValueDist) (O : GenMenu) (M : MDMechanism n) : Prop :=
  MDFeasible O M ∧ MDWellDefined (prior D) M ∧ MDBIC D M ∧ MDInterimIR D M

/-- Expected fee revenue of the intermediary. -/
noncomputable def mdFeeRevenue {n : ℕ} (μ : Measure (Fin n → ℝ)) (M : MDMechanism n) : ℝ :=
  ∫ v, ∑ i, M.fee v i ∂μ

/-- Expected revenue of the seller. -/
noncomputable def mdSellerRevenue {n : ℕ} (μ : Measure (Fin n → ℝ)) (M : MDMechanism n) : ℝ :=
  ∫ v, ∑ i, M.sellerPayment v i ∂μ

noncomputable def mdOptFee {n : ℕ} (D : Fin n → ValueDist) (O : GenMenu) : EReal :=
  sSup {r | ∃ M : MDMechanism n, MDAdmissible D O M ∧ (mdFeeRevenue (prior D) M : EReal) = r}

def MDBestResponse {n : ℕ} (D : Fin n → ValueDist) (O : GenMenu) (M : MDMechanism n) : Prop :=
  MDAdmissible D O M ∧ (mdFeeRevenue (prior D) M : EReal) = mdOptFee D O

/-- `RandMD(O)`: the seller's revenue against the worst intermediary best response,
`⊥` if there is none (the convention of the published `RandMI`). -/
noncomputable def RandMD {n : ℕ} (D : Fin n → ValueDist) (O : GenMenu) : EReal := by
  classical
  exact if ∃ M, MDBestResponse D O M then
    sInf {r | ∃ M, MDBestResponse D O M ∧ (mdSellerRevenue (prior D) M : EReal) = r}
  else ⊥

end LotteryInterm.IID.Supplement


