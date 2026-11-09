-- Prove2me | Definitions.Def_BarelyTestable_LowerBound_Protocol
-- name    : BarelyTestable_LowerBound_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:10.212741+00:00
-- url     : https://prove2.me/theorems/186c4497-66d7-4c89-af0e-138094153556
-- title:
--   Adaptive oracle procedures, run semantics and randomized testers
-- statement:
--   A deterministic procedure receives only its finite history of queried vertices and exact real answers. It either outputs accept/reject or requests its next vertex. The recursive run appends each actual oracle answer to that history; at fuel zero it may still output, but may not make an additional query. Queries may repeat.
--
--   A randomized tester chooses such a procedure using a seed from an arbitrary measurable probability space independent of the oracle. Its acceptance and rejection events for each fixed oracle are measurable. Correctness for a property $P$ requires acceptance probability at least $2/3$ for every member and rejection probability at least $2/3$ for every $\varepsilon$-far function:
--
--   $$\Pr[\mathrm{accept}\ f]\ge2/3\quad(f\in P),\qquad \Pr[\mathrm{reject}\ f]\ge2/3\quad(f\text{ is }\varepsilon\text{-far}).$$
--
--   A budget of $q$ means every oracle and every seed halts after at most $q$ actual queries. No finite budget is assumed in the tester type; an unbounded or nonterminating run precludes such a budget. There is no condition on intermediate-distance functions. This interface counts worst-case queries and allows arbitrary real answers and non-atomic seed laws.
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Definition 2.5, p. 10 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Cube

set_option autoImplicit false

namespace BarelyTestable.LowerBound

abbrev History (ι : Type) := List (Cube ι × ℝ)
abbrev Procedure (ι : Type) := History ι → Bool ⊕ Cube ι

/-- Fuel counts queries, including a final decision after the last query. -/
def run {ι : Type} (A : Procedure ι) (f : Oracle ι) : ℕ → History ι → History ι × Option Bool
  | 0, h => match A h with
    | Sum.inl b => (h, some b)
    | Sum.inr _ => (h, none)
  | k + 1, h => match A h with
    | Sum.inl b => (h, some b)
    | Sum.inr x => run A f k (h ++ [(x, f x)])

def Accepts {ι : Type} (A : Procedure ι) (f : Oracle ι) : Prop :=
  ∃ k, (run A f k []).2 = some true

def Rejects {ι : Type} (A : Procedure ι) (f : Oracle ι) : Prop :=
  ∃ k, (run A f k []).2 = some false

def Budget {ι : Type} (A : Procedure ι) (q : ℕ) : Prop :=
  ∀ f : Oracle ι, (run A f q []).2 ≠ none

/-- All random choices are in a seed independent of the oracle. No finite-seed restriction. -/
structure Tester (ι Ω : Type) [MeasurableSpace Ω] where
  procedure : Ω → Procedure ι
  accept_measurable : ∀ f, MeasurableSet {ω | Accepts (procedure ω) f}
  reject_measurable : ∀ f, MeasurableSet {ω | Rejects (procedure ω) f}

def TesterBudget {ι Ω : Type} [MeasurableSpace Ω] (T : Tester ι Ω) (q : ℕ) : Prop :=
  ∀ ω, Budget (T.procedure ω) q

def Correct {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (T : Tester ι Ω) (P : Oracle ι → Prop) (ε : ℝ) : Prop :=
  (∀ f, P f → (2 / 3 : ℝ) ≤ μ.real {ω | Accepts (T.procedure ω) f}) ∧
  (∀ f, Far P ε f → (2 / 3 : ℝ) ≤ μ.real {ω | Rejects (T.procedure ω) f})

end BarelyTestable.LowerBound


