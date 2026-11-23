-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_PowerFourPadding
-- name    : ITPIRPreproc_MatchVec_PowerFourPadding
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:19.55297+00:00
-- url     : https://prove2.me/theorems/88f1f60f-71e8-4ebd-a058-c98bcd3729b1
-- title:
--   Power-of-four padding lengths and componentwise PIR budget comparison
-- statement:
--   We fix \(h(n)=\max(3,\lceil\log_4 n\rceil)\) and \(N(n)=4^{h(n)}\), together with the exact real-valued budget records used by the power-of-four construction, by a constant-overhead RAM padding wrapper, and by the final theorem. `BudgetLE` compares all seven budget fields componentwise. The helper `meetsBudget_mono` proves that any worst-case RAM cost bound can be weakened componentwise. The wrapper allowance \(A\,n^{1/4}\) covers its fixed program/header costs and working space; it is asymptotically absorbed by exponents at least \(1/2\), while preprocessing also includes the \(A N(n)\) stream-reading cost.
-- source:
--   Dujmovic–Lai–Wichs, STOC 2027 submission #572, proof of Theorem 6.1, PDF p.26: choose a power of four at most 64n and pad the database; §3 and Appendix A for the RAM wrapper costs. The componentwise budget comparison is the formal bookkeeping needed to apply those costs.

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_ITPIRPreproc_MatchVec_Model

open scoped ENNReal
open Filter Topology

namespace ITPIRPreproc.MatchVec

/-- The exponent of the power of four used for a length-`n` database. The floor `3`
ensures applicability of the power-of-four construction even at finitely many small lengths. -/
def padHeight (n : ℕ) : ℕ := max 3 (Nat.clog 4 n)

/-- The length of the database after zero-padding. -/
def padLength (n : ℕ) : ℕ := 4 ^ padHeight n

/-- The power-of-four source budget, with the padded length written as a real number. -/
noncomputable def powerFourBudget (K : ℝ) (c : ℕ) (η : ℕ → ℝ) (h lam : ℕ) : Budget where
  preWork := K * ((4 ^ h : ℕ) : ℝ) ^ (1 + η h) * (lam : ℝ) ^ c
  preSpace := K * ((4 ^ h : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + η h) * (lam : ℝ) ^ c
  online := K * lam * ((4 ^ h : ℕ) : ℝ) ^ (η h)
  offline := K * Real.sqrt (4 ^ h : ℕ)
  clientWork := K * ((4 ^ h : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + η h) * (lam : ℝ) ^ c
  clientSpace := K * ((4 ^ h : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + η h) * (lam : ℝ) ^ c
  serverWork := K * ((4 ^ h : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + η h) * (lam : ℝ) ^ c

/-- Costs after a constant-word-overhead RAM wrapper. Communication is unchanged.
The term `A * padLength n` accounts for preprocessing the padded stream, while `A * n^(1/4)`
is a generous allowance for fixed program headers, storing `n` and `padLength n`, and wrapper work
and working space. It is dominated by every relevant final work/space exponent. -/
noncomputable def adapterBudget (A : ℝ) (n : ℕ) (B : Budget) : Budget where
  preWork := A * B.preWork + A * (padLength n : ℝ) + A * (n : ℝ) ^ ((1 : ℝ) / 4)
  preSpace := A * B.preSpace + A * (n : ℝ) ^ ((1 : ℝ) / 4)
  online := B.online
  offline := B.offline
  clientWork := A * B.clientWork + A * (n : ℝ) ^ ((1 : ℝ) / 4)
  clientSpace := A * B.clientSpace + A * (n : ℝ) ^ ((1 : ℝ) / 4)
  serverWork := A * B.serverWork + A * (n : ℝ) ^ ((1 : ℝ) / 4)

/-- The final budget shape in the statement of Theorem 6.1. -/
noncomputable def targetBudget (C : ℝ) (c : ℕ) (ε : ℕ → ℝ) (n lam : ℕ) : Budget where
  preWork := C * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c
  preSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
  online := C * lam * (n : ℝ) ^ (ε n)
  offline := C * Real.sqrt n
  clientWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
  clientSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
  serverWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c

/-- Componentwise comparison of two RAM cost budgets. -/
def BudgetLE (B B' : Budget) : Prop :=
  B.preWork ≤ B'.preWork ∧ B.preSpace ≤ B'.preSpace ∧ B.online ≤ B'.online ∧
    B.offline ≤ B'.offline ∧ B.clientWork ≤ B'.clientWork ∧
    B.clientSpace ≤ B'.clientSpace ∧ B.serverWork ≤ B'.serverWork

/-- Worst-case budget bounds are monotone in every component. -/
lemma meetsBudget_mono {S : Scheme} {n lam : ℕ} {B B' : Budget}
    (h : BudgetLE B B') (hB : MeetsBudget S n lam B) : MeetsBudget S n lam B' := by
  rcases h with ⟨hw, hs, ho, hoff, hcw, hcs, hsw⟩
  intro D
  rcases hB D with ⟨hpre, hround⟩
  refine ⟨?_, ?_⟩
  · intro τ
    rcases hpre τ with ⟨hhalt, hw', hs'⟩
    exact ⟨hhalt, hw'.trans hw, hs'.trans hs⟩
  · intro st hst i τ
    dsimp only
    rcases hround st hst i τ with ⟨hhalt, hon, hoff', hcw', hqspace, hdspace,
      huspace, hsw'⟩
    exact ⟨hhalt, hon.trans ho, hoff'.trans hoff, hcw'.trans hcw,
      hqspace.trans hcs, hdspace.trans hcs, huspace.trans hcs, hsw'.trans hsw⟩

end ITPIRPreproc.MatchVec


