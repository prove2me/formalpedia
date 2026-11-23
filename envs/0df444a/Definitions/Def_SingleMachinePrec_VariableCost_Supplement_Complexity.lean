-- Prove2me | Definitions.Def_SingleMachinePrec_VariableCost_Supplement_Complexity
-- name    : SingleMachinePrec_VariableCost_Supplement_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:54:18.22766+00:00
-- url     : https://prove2.me/theorems/92e19536-b9cf-439b-b802-9aecad8d31a1
-- title:
--   PTAS, Boolean satisfiability, and bounded-error randomized subexponential SAT algorithms
-- statement:
--   A PTAS is a single computable approximation scheme. For each fixed $m\in\mathbb N$, it computes a deterministic polynomial-time feasible scheduling algorithm of ratio $1+1/(m+1)$ on all instances. These accuracies suffice for every positive requested accuracy; the polynomial may depend on $m$.
--
--   SAT inputs are CNF Boolean formulas, encoded as lists of clauses with binary variable indices and signs. A formula is satisfiable if some truth assignment makes every clause true. The empty conjunction is true and an empty clause is false.
--
--   Randomized subexponential SAT solvability means that for every $\eta>0$ there are finite machines computing a random-tape length and a decision. On every formula, the latter halts on every tape and is correct on at least $2/3$ of the equally likely fair-bit tapes. Both machines and the generation of the bits together run within $2^{n^\eta}$ for all sufficiently large input lengths $n$; all smaller formulas must still be decided with bounded error and finite runtime. The random-tape length is computed by a machine, so it cannot supply advice.
--
--   **Formalization Note** The $2/3$ threshold is the conventional bounded-error normalization of the source's high-probability reduction, with finite exceptions handled separately and amplification allowed. It is not a claimed numerical error bound for Theorem 9.1. Binary CNF encodings are polynomially equivalent to standard SAT encodings; the universal positive exponent absorbs such overhead.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 667, Theorem 9.2 and its proof

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_Scheduling

set_option autoImplicit false

namespace SingleMachinePrec.VariableCost.Supplement

open QAlgorithms.Complexity Computability Turing

/-- A PTAS: one computable scheme, with accuracy `1/(m+1)`, whose specialization
at every fixed m is a deterministic polynomial-time approximation algorithm.
This sequence of accuracies suffices for every positive requested accuracy.
The polynomial may depend on m; no FPTAS runtime bound is imposed. -/
def HasSchedulingPTAS : Prop :=
  ∃ A : ℕ → Str → Str,
    Nonempty (TM2Computable (fun z : ℕ × Str => encBin z.1 ++ z.2) id
      (fun z => A z.1 z.2)) ∧
    ∀ m : ℕ, PolyTimeComputable (A m) ∧
      IsApproxOn SchedInput.enc id SchedInput.IsPoset
        (fun _ => 1 + 1 / ((m : ℝ) + 1)) (A m)

/-- A CNF formula: a conjunction of clauses, each a disjunction of signed variables.
`(i, true)` is a positive literal and `(i, false)` a negative literal. -/
abbrev SATFormula := List (List (ℕ × Bool))

/-- Standard binary CNF input: self-delimiting list lengths and binary variable indices. -/
def SATFormula.enc (φ : SATFormula) : Str :=
  encList (encList (fun l => encBin l.1 ++ [l.2])) φ

/-- Satisfiability of the CNF formula. Empty clauses are false; the empty conjunction is true. -/
def SATFormula.Satisfiable (φ : SATFormula) : Prop :=
  ∃ v : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, v l.1 = l.2

open Classical in
/-- For every η > 0, one finite randomized machine decides SAT in time at most
`2^(n^η)` for all sufficiently large binary input lengths n. It uses `bits n` fair
random bits, halts on every such tape, and is correct with probability at least 2/3
on every formula. A second finite machine computes the tape length from the formula, without advice.
Three times the clock covers this computation, generation of the bits, and the decision.
The threshold allows the usual asymptotic runtime convention and finite exceptions. -/
def HasRandSubexpSAT : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (R M : TM2ComputableAux Bool Bool) (bits time : ℕ → ℕ)
      (out : SATFormula → Str → Bool) (n₀ : ℕ),
      (∀ n, n₀ ≤ n → bits n ≤ time n ∧
        (3 * time n : ℝ) ≤ Real.rpow 2 (Real.rpow (n : ℝ) η)) ∧
      (∀ φ : SATFormula,
        Nonempty (TM2OutputsInTime R.tm (φ.enc.map R.inputAlphabet.symm)
          (some ((encNat (bits φ.enc.length)).map R.outputAlphabet.symm)) (time φ.enc.length))) ∧
      (∀ (φ : SATFormula) (seed : Str), seed.length = bits φ.enc.length →
        Nonempty (TM2OutputsInTime M.tm
          ((φ.enc ++ seed).map M.inputAlphabet.symm)
          (some ([out φ seed].map M.outputAlphabet.symm)) (time φ.enc.length))) ∧
      ∀ φ : SATFormula,
        2 * 2 ^ bits φ.enc.length ≤
          3 * (Finset.univ.filter (fun s : Fin (bits φ.enc.length) → Bool =>
            (out φ (List.ofFn s) = true ↔ φ.Satisfiable))).card

end SingleMachinePrec.VariableCost.Supplement


