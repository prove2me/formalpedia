-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Oracle
-- name    : ChvatalOneHard398_SAT_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:28.115414+00:00
-- url     : https://prove2.me/theorems/307a513c-b674-4d6b-957f-4040b7a6bfb4
-- title:
--   Adaptive deterministic oracle algorithms for promise problems
-- statement:
--   A deterministic oracle algorithm has a next-step map from an input and its preceding answer bits to either one query or an output. Its run appends the oracle's answer after each query and stops at the first output. The stored trace is exactly the queries actually made. The oracle function is never an argument of the next-step map.
--
--   $$\exists A,r\quad\forall\mathrm{orc},x:\quad A^{\mathrm{orc}}(x)\text{ terminates within }r(|x|)\text{ rounds}.$$
--
--   Polynomiality also requires a TM2 polynomial bound for the next-step map on every input/history pair. It therefore charges for writing queries and outputs. Each call costs one further step. Correctness is separate: every oracle correct on the target promise must yield a closest vector on each promised BDD input. The final solver consequence universally quantifies over total polynomial target solvers and requires a total polynomial BDD solver.
--
--   **Formalization Note** The fixed next-step and round polynomials precede the oracle and the input. Restarting a next-step computation from the answer history and summing polynomial costs over polynomially many rounds gives the usual polynomial-time oracle-machine model. Neither the algorithm's data nor its run definition contains a correctness assertion.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.8, §2, Promise problems; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT
open OnlineCRS.Combine

/-- A deterministic next-step algorithm; it has no semantic correctness fields and cannot
inspect the oracle function. Left is a query; right is an output. -/
structure OracleAlg (I Q O : Type) where
  next : I × List Bool → Q ⊕ O

structure OracleRun (Q O : Type) where
  output : Option O
  queries : List Q

/-- History is precisely the preceding answer bits; one oracle call adds one bit. -/
def oracleRun {I Q O : Type} (A : OracleAlg I Q O) (orc : Q → Bool)
    (x : I) : ℕ → List Bool → OracleRun Q O
  | 0, _ => ⟨none,[]⟩
  | k+1, history =>
    match A.next (x,history) with
    | .inr out => ⟨some out,[]⟩
    | .inl q =>
      let tail := oracleRun A orc x k (history ++ [orc q])
      ⟨tail.output,q :: tail.queries⟩

def encStepIn {I : Type} (ei : I → List Sym) (z : I × List Bool) : List Sym :=
  frame (ei z.1) ++ encList encBool z.2

def encStepOut {Q O : Type} (eq : Q → List Sym) (eo : O → List Sym) : Q ⊕ O → List Sym
  | .inl q => 0 :: eq q
  | .inr o => 1 :: eo o

/-- Fixed polynomials before every raw input and every oracle, including non-promise inputs.
The next-step TM cost charges for writing queries and outputs; calls cost one additional step. -/
def IsPolyOracle {I Q O : Type} (ei : I → List Sym) (eq : Q → List Sym) (eo : O → List Sym)
    (A : OracleAlg I Q O) (rounds : Polynomial ℕ) : Prop :=
  PolyTime (encStepIn ei) (encStepOut eq eo) A.next ∧
  ∀ (orc : Q → Bool) (x : I),
    ∃ v, (oracleRun A orc x (rounds.eval (ei x).length) []).output = some v

noncomputable def CorrectOracle (promise : Formula → Prop) (orc : Formula → Bool) : Prop :=
  ∀ F, promise F → (orc F = true ↔ Satisfiable F)

noncomputable def SolvesBDDWith (A : OracleAlg BDDInput Formula (List ℚ))
    (rounds : Polynomial ℕ) (promise : Formula → Prop) : Prop :=
  ∀ orc, CorrectOracle promise orc → ∀ x, BDDPromise x →
    ∃ v, (oracleRun A orc x (rounds.eval (encBDD x).length) []).output = some v ∧ BDDCorrect x v

noncomputable def BDDReduction (promise : Formula → Prop) : Prop :=
  ∃ (A : OracleAlg BDDInput Formula (List ℚ)) (rounds : Polynomial ℕ),
    IsPolyOracle encBDD encFormula encOutput A rounds ∧ SolvesBDDWith A rounds promise

noncomputable def SolverConsequence : Prop :=
  ∀ f : Formula → Bool, PolyTime encFormula encBool f → CorrectOracle TargetPromise f →
    ∃ g : BDDInput → List ℚ, PolyTime encBDD encOutput g ∧ ∀ x, BDDPromise x → BDDCorrect x (g x)

end ChvatalOneHard398.SAT


