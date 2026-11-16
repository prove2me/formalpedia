-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Supplement_BitTasks
-- name    : LogSupermodularBIS_Main_Supplement_BitTasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:33:23.164764+00:00
-- url     : https://prove2.me/theorems/bb647733-7696-4d9e-a29e-0609ec2cc588
-- title:
--   Bit input layouts, exact weight access and five task specifications
-- statement:
--   The mathematical graph and weight models are the published base definitions. Weight input consists of the dimension $d$, value-length bound $B$, and rational accuracy parameters. Its sole external operation receives exactly $d$ configuration bits and returns the canonical code of $W(x)$, charged $T_W$ plus the lengths of the query and answer. A malformed query returns no weight information and pays for scanning its input. The evaluator time bound is not an input or advice. Graph input consists of the vertex count, the labeled adjacency matrix and rational parameters, and has no external evaluator.
--
--   Let $\ell_{\rm par}$ be the total length of the parameter codes for this invocation. Write
--   $$
--   E_G=n^{1/3}(\log n)^{4/3},\qquad
--   E_W=\min\{d,d^{1/3}(\log d)^{2/3}(\log(d+B))^{2/3}\}.
--   $$
--   Uniform asymptotic bounds have the form
--   $$
--   C\exp(CE)(1+\textstyle\sum\text{parameters})^a(1+\ell_{\rm par})^b.
--   $$
--   The theorem quantifies $C>0$ and natural degrees $a,b$ before all instances and requested errors.
--
--   A sampling specification requires explicit halting and a valid configuration on every bit tape, plus total variation at most $\eta$ from the target law. Graph sampling additionally requires independence of the output set on every tape. A counting specification requires a canonical rational output on every tape and relative error at most $\epsilon$ with probability at least $1-\delta$. The additive specification instead requires
--   $$
--   \Pr[\log Z_W-\epsilon d-1/8\le A\le\log Z_W]\ge1-\delta.
--   $$
--   The additive output may be negative; its target is the actual partition function, including the contribution $\log W(0)$. All laws and costs are computed from binary-stack executions, and all runtime bounds are pathwise. These interfaces introduce no partition-function, marginal or optimization oracle.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 38 (PDF 39), Theorem A.1; pp. 2–3 and 12 (PDF 3–4 and 13), Theorems 1.1–1.2 and Corollary 2.3

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Supplement_FiniteChoice
import Definitions.Def_LogSupermodularBIS_Main_Algorithms

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- The only non-graph oracle: exact evaluation of the supplied weight at one configuration.
A query is exactly `d` bits; an answer is an actual rational code. Reading the query and
writing the answer are charged in addition to the evaluator's stated bit cost `TW`.
Malformed queries return no information and are charged for scanning their input. -/
def weightBitOracle {d : ℕ} (W : (Fin d → Bool) → ℚ) (TW : ℕ) : BitOracle :=
  some fun bs =>
    if bs.length = d then
      let answer := encRat (W fun i => bs.getD i.val false)
      (answer, TW + bs.length + answer.length)
    else ([], bs.length + 1)

/-- Rational accuracy/failure parameters concatenated with self-delimiting codes. -/
def encParameters (par : List ℚ) : Bits := (par.map encRat).flatten

/-- Total binary encoding length of the parameters for this invocation, distinct from `B`. -/
def parameterLength (par : List ℚ) : ℕ := (encParameters par).length

/-- Weight algorithms see dimension, value-length bound, and rational parameters. `TW` is a
cost bound, not advice supplied to the program. All access to `W` is through the evaluator. -/
def weightBitInput (d B : ℕ) (par : List ℚ) : Bits :=
  encNat d ++ encNat B ++ encParameters par

open Classical in
/-- Graph input: vertex count, row-major adjacency bits, and rational parameters. No oracle
or supplied bipartition is present; the graph is finite, labeled and simple. -/
noncomputable def graphBitInput {n : ℕ} (G : SimpleGraph (Fin n)) (par : List ℚ) : Bits :=
  encNat n ++ (List.ofFn fun k : Fin (n * n) =>
    decide (G.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) ++ encParameters par

/-- Sampling: halting and valid configurations on every tape, plus TV accuracy of the
execution-derived law. The graph task additionally requires independent output configurations. -/
def BitSamples (P : BitProgram) (O : BitOracle) (input : Bits) (d : ℕ)
    (target : (Fin d → Bool) → ℝ) (valid : (Fin d → Bool) → Prop) (η T : ℝ) : Prop :=
  BitTerminates P O input T (fun bs => ∃ x : Fin d → Bool, bs = List.ofFn x ∧ valid x) ∧
  finiteTV (fun x : Fin d → Bool => bitMass P O input T (List.ofFn x)) target ≤ η

/-- Relative counting: rational output on every tape; only the relative-error event may fail. -/
def BitCounts (P : BitProgram) (O : BitOracle) (input : Bits) (Z ε δ T : ℝ) : Prop :=
  BitTerminates P O input T (fun bs => ∃ q : ℚ, bs = encRat q) ∧
  1 - δ ≤ bitProbability P O input T (fun bs =>
    ∃ q : ℚ, bs = encRat q ∧ |(q : ℝ) / Z - 1| ≤ ε)

/-- One-sided additive estimation of the actual log partition function. Outputs may be
negative; no clamp or normalization removes `log W(0)`. -/
def BitAdditive (P : BitProgram) (O : BitOracle) (input : Bits)
    (d : ℕ) (Z ε δ T : ℝ) : Prop :=
  BitTerminates P O input T (fun bs => ∃ q : ℚ, bs = encRat q) ∧
  1 - δ ≤ bitProbability P O input T (fun bs =>
    ∃ q : ℚ, bs = encRat q ∧ Real.log Z - ε * d - 1 / 8 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Real.log Z)

/-- Rational source parameter range `(0,1/2]`. -/
def HalfAccuracy (r : ℚ) : Prop := 0 < r ∧ r ≤ 1 / 2

/-- Graph exponential scale of Theorem 1.1. Powers are real powers. -/
noncomputable def graphExponent (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log n) ^ (4 / 3 : ℝ)

/-- Full minimum exponent of Theorem 1.2, with unrestricted `B`. -/
noncomputable def weightExponent (d B : ℕ) : ℝ :=
  min (d : ℝ) ((d : ℝ) ^ (1 / 3 : ℝ) * (Real.log d) ^ (2 / 3 : ℝ) *
    (Real.log ((d : ℝ) + B)) ^ (2 / 3 : ℝ))

/-- Uniform interpretation of the source asymptotics, with a separate parameter-length
polynomial. `C,a,b` are always quantified before instances and accuracy parameters. -/
noncomputable def bitBound (C : ℝ) (a b : ℕ) (E : ℝ) (parameters : List ℝ)
    (par : List ℚ) : ℝ :=
  C * Real.exp (C * E) * (1 + parameters.sum) ^ a * (1 + (parameterLength par : ℝ)) ^ b

end LogSupermodularBIS.Main.Supplement


