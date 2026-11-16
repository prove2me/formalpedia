-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_CNF
-- name    : QuantumSepPoly_Frobenius_Supplement_CNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:45:31.523203+00:00
-- url     : https://prove2.me/theorems/7e505d4e-38f8-405b-84ac-ce0ea7141db9
-- title:
--   3-CNF inputs and uniform resource bounds
-- statement:
--   A 3-CNF input retains $m$ indexed clauses, each with at most three signed variable occurrences (empty clauses included) from $[n]$; repeated literals and clauses are allowed. Its ordinary satisfiability uses the published general CNF definition, without changing the input size or erasing occurrences in the machine input. Natural and real registers contain $n,m$ and every variable/sign pair. No satisfying assignment is loaded.
--
--   With $L=n+m+2$, polynomial and soft-exponential witnesses mean $CL^e$ and $2^{C\sqrt L(\log_2L)^a}$ with positive coefficients and natural exponents chosen before inputs. First-halting execution cost is infinite on nontermination. This supplies the input and resource interface for both existential algorithm statements.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 24, 25, 29 (PDF p. 24, 25, 29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_QuantumSepPoly_Frobenius_RealRAM

noncomputable section
open scoped ENNReal

namespace QuantumSepPoly.Frobenius.Supplement
/-- At most three literal occurrences per clause, including empty clauses.
Repeated clauses and literals remain allowed. -/
abbrev CNF3 (n m : ℕ) := Fin m → {l : List (Fin n × Bool) // l.length ≤ 3}

def cnfFormula {n m : ℕ} (f : CNF3 n m) : LiftSAParity.CNF (Fin n) :=
  Finset.univ.image (fun j => (f j).val.toFinset)

def Satisfiable {n m : ℕ} (f : CNF3 n m) : Prop :=
  LiftSAParity.Satisfiable (cnfFormula f)

/-- n[0]=n, n[1]=m, then variable/sign pairs in clause-major order.
Both natural and scalar views are loaded; no witness is supplied. -/
def cnfInput {n m : ℕ} (f : CNF3 n m) : RAMState :=
  let data := [n,m] ++ ((List.finRange m).flatMap fun j =>
    [(f j).val.length] ++ ((f j).val.flatMap fun a => [a.1.val, if a.2 then 1 else 0]))
  { pc := 0, nat := fun i => data[i]?.getD 0,
    real := fun i => (data[i]?.getD 0 : ℝ), randomIndex := 0,
    cost := data.length, stopped := false }

def inputSize (n m : ℕ) : ℝ := n + m + 2

def polyBound (C : ℝ) (e n m : ℕ) : ℝ := C * inputSize n m ^ e

def softExpBound (C : ℝ) (a n m : ℕ) : ℝ :=
  (2 : ℝ) ^ (C * Real.sqrt (inputSize n m) * (Real.logb 2 (inputSize n m)) ^ a)

/-- First-halting runtime, infinity on nontermination; used for expected cost. -/
def executionCost (P : RAMProgram) (initial : RAMState) (r : RandomTape) : ℝ≥0∞ :=
  if (ramResult P initial r).stopped then (ramResult P initial r).cost else ⊤
end QuantumSepPoly.Frobenius.Supplement


