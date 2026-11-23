-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Hardness
-- name    : SkutellaCQP_MaxSNP_Supplement_Hardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:49:26.670579+00:00
-- url     : https://prove2.me/theorems/1e8d4601-bbc1-457f-8b5a-62e3ae40383e
-- title:
--   §7 — the full target scheduling problem and the actual encoded R and SAT maps
-- statement:
--   The target problem is the full unrelated-machine problem with job-dependent release dates and unweighted total completion time. A finite input specifies arbitrary nonnegative rational processing times and release dates, eligibility via optional processing times, and at least one eligible machine for each job. Zero processing times and forbidden machines are retained. Solutions specify rational start times and machine choices and satisfy the published nonoverlap convention. The objective is
--   $$\operatorname{VAL}(S)=\sum_j(S_j+p_{\sigma(j)j}).$$
--   The infimum over rational schedules equals the real-time optimum: left-justifying a fixed job order on each machine uses only rational data and never increases any completion time.
--
--   The source wrapper reuses the published 3-occurrence clause model, its validity, truth semantics and satisfaction count. The actual map $R$ reuses its eligibility: variable jobs require four time units and release at zero; clause jobs require zero time and release at three. Recovered truth is the true/false machine of each variable job, exactly SAT from the source. An unused, ineligible dummy machine makes the empty instance a valid encoded scheduling input and changes no feasible value. Dense incidence tables are polynomially equivalent to the source's sparse clauses because validity gives $n\le3m$.
--
--   The specification of the source L-reduction fixes these very maps and constants $32,1$. Theorem 7.2 asserts their polynomial computability and correctness and establishes source and target hardness unconditionally.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 32–33, 3-OCCURRENCE MAX3SAT, R, SAT and Theorem 7.2

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Complexity
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP.Supplement

open Finset

/-- General unrelated-machine scheduling input, not just a reduction gadget. `none` means
forbidden (infinite processing time); zero finite processing times are allowed in §7. -/
structure SchedulingInput where
  m : ℕ
  n : ℕ
  machines_pos : 0 < m
  p : Fin m → Fin n → Option ℚ
  r : Fin n → ℚ

def SchedulingInput.Valid (I : SchedulingInput) : Prop :=
  (∀ i j t, I.p i j = some t → 0 ≤ t) ∧
  (∀ j, 0 ≤ I.r j) ∧ (∀ j, ∃ i t, I.p i j = some t)

def optionRatCode : Option ℚ → List Bool
  | none => [false]
  | some q => true :: ratCode q

def SchedulingInput.code (I : SchedulingInput) : List Bool :=
  natCode I.m ++ natCode I.n ++
  listCode optionRatCode ((List.finRange I.m).flatMap fun i => (List.finRange I.n).map (I.p i)) ++
  listCode ratCode ((List.finRange I.n).map I.r)

/-- Finitely encoded arbitrary rational nonpreemptive schedule. -/
structure SchedulingOutput where
  machine : List ℕ
  start : List ℚ

def SchedulingOutput.code (o : SchedulingOutput) : List Bool :=
  listCode natCode o.machine ++ listCode ratCode o.start

def SchedulingOutput.mach (I : SchedulingInput) (o : SchedulingOutput) (j : Fin I.n) : Fin I.m :=
  ⟨o.machine[j.val]?.getD 0 % I.m, Nat.mod_lt _ I.machines_pos⟩

def SchedulingOutput.begin (o : SchedulingOutput) (j : ℕ) : ℚ := o.start[j]?.getD 0

def SchedulingOutput.processing (I : SchedulingInput) (o : SchedulingOutput) (j : Fin I.n) : ℚ :=
  (I.p (o.mach I j) j).getD 0

/-- Full scheduling feasibility. The zero-job convention is exactly the published one:
a zero-length job conflicts with the interior of another job. -/
def SchedulingOutput.Feasible (I : SchedulingInput) (o : SchedulingOutput) : Prop :=
  o.machine.length = I.n ∧ o.start.length = I.n ∧
  (∀ j : Fin I.n, o.machine[j.val]?.getD 0 < I.m) ∧
  (∀ j, (I.p (o.mach I j) j).isSome = true) ∧
  (∀ j : Fin I.n, I.r j ≤ o.begin j.val) ∧
  (∀ j k : Fin I.n, j ≠ k → o.mach I j = o.mach I k →
    o.begin j.val + o.processing I j ≤ o.begin k.val ∨
    o.begin k.val + o.processing I k ≤ o.begin j.val)

/-- The full unweighted scheduling problem `R | r_j | ∑ C_j` on finite binary inputs.
Its real optimum equals the rational one by left-justifying each machine's job order. -/
noncomputable def schedulingProblem : OptimizationProblem where
  Input := SchedulingInput
  Solution := SchedulingOutput
  inputCode := SchedulingInput.code
  solutionCode := SchedulingOutput.code
  valid := SchedulingInput.Valid
  feasible := SchedulingOutput.Feasible
  value := fun I o => (∑ j : Fin I.n, (o.begin j.val + o.processing I j) : ℚ)
  minimize := true

/-- Source instance wrapper reusing the immutable clause model. Validity is the published
one, including removal of unused varCount. Empty instances are included. -/
structure SatInput where
  varCount : ℕ
  clauses : ℕ
  formula : SkutellaCQP.MaxSNP.Occ3Max3Sat varCount clauses

/-- Explicit clause/literal incidence table. On valid 3-occurrence inputs its dense size is
polynomially equivalent to the sparse clause list since n≤3m. -/
def SatInput.code (I : SatInput) : List Bool :=
  natCode I.varCount ++ natCode I.clauses ++
  ((List.finRange I.clauses).flatMap fun c =>
    (List.finRange I.varCount).flatMap fun x =>
      [decide ((x, false) ∈ I.formula.clause c), decide ((x, true) ∈ I.formula.clause c)])

def SatInput.truth (I : SatInput) (s : List Bool) (x : Fin I.varCount) : Bool := s[x.val]?.getD false

/-- The cited 3-OCCURRENCE MAX3SAT optimization problem, with the published validity,
clause count and truth semantics unchanged. -/
noncomputable def occurrenceSatProblem : OptimizationProblem where
  Input := SatInput
  Solution := List Bool
  inputCode := SatInput.code
  solutionCode := listCode fun b : Bool => [b]
  valid := fun I => I.formula.IsValid
  feasible := fun I s => s.length = I.varCount
  value := fun I s => (SkutellaCQP.MaxSNP.satCount I.formula (I.truth s) : ℝ)
  minimize := false

/-- Identify the ordered job table with the original v-jobs and c-jobs. -/
def SatInput.job (I : SatInput) (j : Fin (I.varCount + I.clauses)) :
    SkutellaCQP.MaxSNP.Job I.varCount I.clauses :=
  if h : j.val < I.varCount then Sum.inl ⟨j.val, h⟩
  else Sum.inr ⟨j.val - I.varCount, by omega⟩

/-- Even machine 2x is x's true machine, odd machine 2x+1 its false machine.
One extra, never eligible, dummy machine handles the empty instance without a zero-machine
computational type; it changes no feasible schedule or value. -/
def SatInput.machine (I : SatInput) (i : Fin (2 * I.varCount + 1)) :
    Option (SkutellaCQP.MaxSNP.Machine I.varCount) :=
  if h : i.val / 2 < I.varCount then some (⟨i.val / 2, h⟩, decide (i.val % 2 = 0)) else none

/-- The actual reduction R: exactly the published eligibility and releases, with rational
4/0 processing requirements and an unused dummy machine for the empty boundary. -/
noncomputable def reductionR (I : SatInput) : SchedulingInput where
  m := 2 * I.varCount + 1
  n := I.varCount + I.clauses
  machines_pos := by omega
  p := fun i j => by
    classical
    exact match I.machine i with
    | none => none
    | some x => if SkutellaCQP.MaxSNP.Eligible I.formula (I.job j) x
        then some (match I.job j with | .inl _ => 4 | .inr _ => 0) else none
  r := fun j => match I.job j with | .inl _ => 0 | .inr _ => 3

/-- Recover the original truth assignment SAT(S) from the machine of each v-job. -/
def reductionSAT (x : SatInput × SchedulingOutput) : List Bool :=
  List.ofFn fun j : Fin x.1.varCount => decide ((x.2.machine[j.val]?.getD 0) % 2 = 0)

/-- The concrete 32,1 L-reduction from §7. This predicate is a specification only;
Theorem 7.2 asserts that it is inhabited, with genuine Turing-machine implementations. -/
def IsSourceReduction (R : LReduction occurrenceSatProblem schedulingProblem) : Prop :=
  R.α = 32 ∧ R.β = 1 ∧ R.forward = reductionR ∧ R.backward = reductionSAT

end SkutellaCQP.MaxSNP.Supplement


