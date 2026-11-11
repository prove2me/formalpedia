-- Prove2me | Definitions.Def_LotteryInterm_IID_Mechanism
-- name    : LotteryInterm_IID_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:46.144197+00:00
-- url     : https://prove2.me/theorems/d6ba4664-0178-4739-9227-d17698c7ecf9
-- title:
--   Direct mechanisms, BIC, interim IR and optimal revenue
-- statement:
--   For $n$ bidders a direct mechanism consists of access probabilities $y_i(v)$ and payments $q_i(v)$ on real report profiles. Feasibility requires $y_i\ge0$ and $\sum_i y_i\le1$. Measurability and integrability are required both under the prior and on every section obtained by fixing one report. For a valuation function $w$, let $Y_i(t)$ and $Q_i(t)$ be interim allocation and payment, averaging over independent opponents.
--
--   Admissibility requires Bayesian incentive compatibility against every real report and interim individual rationality, for almost every truthful type:
--   $$Y_i(t)w(t)-Q_i(t)\ge Y_i(t')w(t)-Q_i(t'),\qquad Y_i(t)w(t)-Q_i(t)\ge0.$$
--   Revenue is the expectation of total payments. Its supremum over admissible mechanisms is $\operatorname{OptRev}(F,w)$, an extended real. Define $\operatorname{OPT}=\operatorname{OptRev}(F,\mathrm{id})$ and $\operatorname{OPT}_p=\operatorname{OptRev}(F,(\cdot-p)^+)$. They are not defined by virtual-surplus formulas.
--
--   The canonical lowest utility is zero when every positive utility threshold has positive probability of being undercut. Under BIC and IR this is precisely zero essential lower-endpoint utility, including pure point masses. It avoids reading arbitrary changes at a null lowest report as the utility normalization. The module also defines virtual surplus and the nonnegative maximum virtual value.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §2, pp.7–8 (PDF pp.8–9); §3.1, p.9 (PDF p.10); Theorem A.8, pp.39–40 (PDF pp.40–41); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_ValueDist

open MeasureTheory
open scoped ENNReal

namespace LotteryInterm.IID

/-- A general direct single-item mechanism; feasibility and BIC are separate
predicates, so this data type does not assume any optimality conclusion. -/
structure Mechanism (n : ℕ) where
  allocation : (Fin n → ℝ) → Fin n → ℝ
  payment : (Fin n → ℝ) → Fin n → ℝ

def Feasible {n : ℕ} (M : Mechanism n) : Prop :=
  (∀ v i, 0 ≤ M.allocation v i) ∧
  (∀ v, (∑ i, M.allocation v i) ≤ 1)

def WellDefined {n : ℕ} (μ : Measure (Fin n → ℝ)) (M : Mechanism n) : Prop :=
  (∀ i, Measurable (fun v => M.allocation v i)) ∧
  (∀ i, Measurable (fun v => M.payment v i)) ∧
  (∀ i, Integrable (fun v => M.allocation v i) μ) ∧
  (∀ i, Integrable (fun v => M.payment v i) μ) ∧
  (∀ i t, Integrable (fun v => M.allocation (Function.update v i t) i) μ) ∧
  (∀ i t, Integrable (fun v => M.payment (Function.update v i t) i) μ)

noncomputable def interimAllocation {n : ℕ} (μ : Measure (Fin n → ℝ))
    (M : Mechanism n) (i : Fin n) (t : ℝ) : ℝ :=
  ∫ v, M.allocation (Function.update v i t) i ∂μ

noncomputable def interimPayment {n : ℕ} (μ : Measure (Fin n → ℝ))
    (M : Mechanism n) (i : Fin n) (t : ℝ) : ℝ :=
  ∫ v, M.payment (Function.update v i t) i ∂μ

noncomputable def interimUtility {n : ℕ} (μ : Measure (Fin n → ℝ)) (w : ℝ → ℝ)
    (M : Mechanism n) (i : Fin n) (t : ℝ) : ℝ :=
  interimAllocation μ M i t * w t - interimPayment μ M i t

def BIC {n : ℕ} (D : Fin n → ValueDist) (w : ℝ → ℝ) (M : Mechanism n) : Prop :=
  ∀ i, ∀ᵐ t ∂(D i).law, ∀ report : ℝ,
    interimAllocation (prior D) M i report * w t -
      interimPayment (prior D) M i report ≤ interimUtility (prior D) w M i t

def InterimIR {n : ℕ} (D : Fin n → ValueDist) (w : ℝ → ℝ) (M : Mechanism n) : Prop :=
  ∀ i, ∀ᵐ t ∂(D i).law, 0 ≤ interimUtility (prior D) w M i t

def Admissible {n : ℕ} (D : Fin n → ValueDist) (w : ℝ → ℝ) (M : Mechanism n) : Prop :=
  Feasible M ∧ WellDefined (prior D) M ∧ BIC D w M ∧ InterimIR D w M

noncomputable def revenue {n : ℕ} (μ : Measure (Fin n → ℝ)) (M : Mechanism n) : ℝ :=
  ∫ v, ∑ i, M.payment v i ∂μ

noncomputable def OptRev {n : ℕ} (D : Fin n → ValueDist) (w : ℝ → ℝ) : EReal :=
  sSup {r | ∃ M : Mechanism n, Admissible D w M ∧ (revenue (prior D) M : EReal) = r}

noncomputable def OPT {n : ℕ} (D : Fin n → ValueDist) : EReal := OptRev D id
noncomputable def shiftedOPT {n : ℕ} (D : Fin n → ValueDist) (p : ℝ) : EReal :=
  OptRev D (fun t => max (t - p) 0)

/-- Lowest-type utility of the canonical BIC representative: its essential lower
endpoint is zero. This is invariant under changes at null types, unlike evaluating
an arbitrary a.e.-BIC mechanism at a single lower endpoint. -/
def ZeroLowestUtility {n : ℕ} (D : Fin n → ValueDist) (M : Mechanism n) : Prop :=
  ∀ i, ∀ ε : ℝ, 0 < ε →
    0 < (D i).law {t | interimUtility (prior D) id M i t < ε}

noncomputable def virtualSurplus {n : ℕ} (D : Fin n → ValueDist)
    (M : Mechanism n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, virtualValue (D i) (v i) * M.allocation v i

noncomputable def maxVirtual {n : ℕ} (D : Fin n → ValueDist)
    (v : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset (Option (Fin n))).Nonempty)
    (fun i => match i with | none => 0 | some j => virtualValue (D j) (v j))

end LotteryInterm.IID


