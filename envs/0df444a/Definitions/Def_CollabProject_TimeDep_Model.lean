-- Prove2me | Definitions.Def_CollabProject_TimeDep_Model
-- name    : CollabProject_TimeDep_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:06.864839+00:00
-- url     : https://prove2.me/theorems/1b16483a-d244-4d7b-b755-9e54b28cb96c
-- title:
--   Two-firm serial project with time-dependent delay penalties and asymmetric information
-- statement:
--   A supplier (firm 1) performs the first task of a serial project, followed by a manufacturer (firm 0). Each keeps the benchmark task duration or delays by one period. A delayed task adds one period to project duration, so total delay is zero, one, or two periods. Supplier and manufacturer savings are $s_1,s_0$; their shares of the first-period penalty are $p^1_1,p^1_0$, and of the second-period penalty $p^2_1,p^2_0$. A firm's payoff is its own saving, if it delays, less its share of the total project penalty. Thus, for example, when both delay the supplier receives $s_1-p^1_1-p^2_1$ and the manufacturer receives $s_0-p^1_0-p^2_0$.
--
--   The model includes Condition 2: both savings are below $p^1=p^1_1+p^1_0$, while $p^1<p^2=p^2_1+p^2_0$ and each firm's second-period share exceeds its first-period share. It represents the supplier's belief by finitely many possible manufacturer types and nonnegative weights summing to one. The masses $q^l_0,q^m_0,q^h_0$ are computed from the low, medium, and high saving classes of those types. Under asymmetric information the supplier maximizes expected payoff against each believed type's best response, while the true manufacturer responds after seeing the supplier's action.
--
--   A selected supplier decision maximizes expected payoff and chooses keep if both actions tie. These definitions support both the symmetric-information equilibrium table and the asymmetric-information comparison.
--
--   **Formalization Note** The fields `s1`, `s0`, `p11`, `p21`, `p10`, `p20` put period before firm in penalty indices. The standing predicate explicitly requires positive savings; genericity is a separate predicate excluding payoff ties. Monetary values are real, and project delay is a natural number.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), pp. 7–17 (PDF 7–17), §§3–5.1, Assumption 1(b), Condition 2, Assumption 2; Appendix p. 1 (PDF 33), Figure 5b

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Game

namespace CollabProject.TimeDep

inductive Act | keep | delay
  deriving DecidableEq

instance : Fintype Act := ⟨{.keep, .delay}, by intro x; cases x <;> simp⟩

/-- The supplier is firm 1. The first digit of each penalty field denotes the
period of project delay; the second digit denotes the firm. -/
structure SType where
  s1 : ℝ
  p11 : ℝ
  p21 : ℝ

/-- The manufacturer is firm 0. -/
structure MType where
  s0 : ℝ
  p10 : ℝ
  p20 : ℝ

def Act.delayPeriods : Act → ℕ
  | .keep => 0
  | .delay => 1

/-- In the serial project, each delayed task adds one period. -/
def delayCount (a1 a0 : Act) : ℕ := a1.delayPeriods + a0.delayPeriods

/-- A firm pays its first-period share for one period of project delay and
both shares for two periods. -/
def penalty (pA pB : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => pA
  | _ => pA + pB

def u1 (S : SType) (a1 a0 : Act) : ℝ :=
  (if a1 = .delay then S.s1 else 0) - penalty S.p11 S.p21 (delayCount a1 a0)

def u0 (M : MType) (a1 a0 : Act) : ℝ :=
  (if a0 = .delay then M.s0 else 0) - penalty M.p10 M.p20 (delayCount a1 a0)

/-- Assumption 1(b), Condition 2, and positive direct-cost savings. -/
def Standing (S : SType) (M : MType) : Prop :=
  0 < S.s1 ∧ 0 < M.s0 ∧
  S.s1 < S.p11 + M.p10 ∧ M.s0 < S.p11 + M.p10 ∧
  S.p11 + M.p10 < S.p21 + M.p20 ∧ S.p11 < S.p21 ∧ M.p10 < M.p20

/-- Excludes the payoff ties omitted from the paper's strict case table. -/
def Generic (S : SType) (M : MType) : Prop :=
  M.s0 ≠ M.p10 ∧ M.s0 ≠ M.p20 ∧ S.s1 ≠ S.p11 ∧ S.s1 ≠ S.p21

def game (S : SType) (M : MType) : SequentialGame Act Act :=
  ⟨u1 S, u0 M⟩

def IsBR0 (M : MType) (a1 a0 : Act) : Prop :=
  SequentialGame.IsBR0 (u0 M) a1 a0

def IsSPNE (S : SType) (M : MType) (a1 : Act) (σ0 : Act → Act) : Prop :=
  (game S M).IsSPNE a1 σ0

/-- The supplier's finite-support prior over manufacturer cost types. -/
structure Belief (ι : Type) [Fintype ι] where
  θ : ι → MType
  w : ι → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1

/-- A manufacturer type belongs to exactly one of Assumption 2's three
savings classes. -/
def MType.Classed (T : MType) : Prop :=
  T.p10 < T.p20 ∧ T.s0 ≠ T.p10 ∧ T.s0 ≠ T.p20

variable {ι : Type} [Fintype ι]

noncomputable def qLow (B : Belief ι) : ℝ :=
  ∑ i, if (B.θ i).s0 < (B.θ i).p10 then B.w i else 0

noncomputable def qMid (B : Belief ι) : ℝ :=
  ∑ i, if (B.θ i).p10 < (B.θ i).s0 ∧ (B.θ i).s0 < (B.θ i).p20 then B.w i else 0

noncomputable def qHigh (B : Belief ι) : ℝ :=
  ∑ i, if (B.θ i).p20 < (B.θ i).s0 then B.w i else 0

def expU1 (S : SType) (B : Belief ι) (σ : ι → Act → Act) (a1 : Act) : ℝ :=
  ∑ i, B.w i * u1 S a1 (σ i a1)

/-- The supplier's payoff-maximizing decision with the paper's "keep otherwise"
selection when the two expected payoffs are equal. -/
def IsChosenAction (S : SType) (B : Belief ι)
    (σ : ι → Act → Act) (a1 : Act) : Prop :=
  (∀ b, expU1 S B σ b ≤ expU1 S B σ a1) ∧
    (expU1 S B σ .keep = expU1 S B σ .delay → a1 = .keep)

/-- Each believed manufacturer type best-responds; the supplier maximizes
expected payoff; the actual manufacturer best-responds after observing the
supplier's action. -/
def IsAsymEq (S : SType) (B : Belief ι) (M : MType)
    (b1 : Act) (σ : ι → Act → Act) (τ0 : Act → Act) : Prop :=
  (∀ i a, IsBR0 (B.θ i) a (σ i a)) ∧
  (∀ a, IsBR0 M a (τ0 a)) ∧
  ∀ b, expU1 S B σ b ≤ expU1 S B σ b1

end CollabProject.TimeDep


