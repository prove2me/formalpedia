-- Prove2me | Definitions.Def_SelectedSubset3SUM_Integer_AllQueries
-- name    : SelectedSubset3SUM_Integer_AllQueries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:39.237052+00:00
-- url     : https://prove2.me/theorems/b42f516d-1093-4449-b656-81c7973e10e1
-- title:
--   Joint-error integer runs and the full unbalanced cost formulas
-- statement:
--   Run a finite published word-RAM program on the packed integer lists and a natural reduction-parameter header. Negative memory initially holds the published independent fair-bit tape. Query output cells start with the non-Boolean value $2$; a successful run halts accepting and gives a Boolean in each output cell, true exactly for membership in the original sumset. All input words, instructions and output materialization are charged.
--
--   A Monte Carlo resource guarantee requires termination by the supplied budget on every tape. The measurable bad event is failure of the whole successful-output specification, including a rejected run. Its probability is at most $K/\max(1,N)$, and empty-side inputs must be correct on every tape.
--
--   For positive side sizes $a,b$, put $h=\sqrt{ab}$. The corollary cost is exactly
--
--   $$h^{393/200}+(a+b)h^{899/1000}+ch^{193/200}.$$
--
--   If a side is empty it is $a+b+c+1$, allowing exact negative answers and input/output traversal. The conditional reduction cost is the full three-term expression
--
--   $$\frac{\widehat n^2}{\binom d{2t}}(P(N,d,t)+N)+N\frac{\widehat n}{2^t}+|C|\frac{\widehat n}{2^t}(Q(N,d,t)+1),$$
--
--   with $d=\lceil t+\lg\widehat n+\lg\lg N+1\rceil$. Its soft-O overhead is an actual fixed power of $1+\lg\max(2,N)$. These are resource specifications to establish from program execution, not instructions that perform semantic set operations for free.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 2.3, pp.6–7; truncation and amplification, pp.8–9; Corollary 2.4, p.9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Mathlib
import Definitions.Def_BddExp3SUM_CoinRAM
import Definitions.Def_SelectedSubset3SUM_Integer_SubsetMachine

namespace SelectedSubset3SUM.Integer

/-! Every output is a Boolean for one original integer query, not a modular answer.
The header contains the reduction parameter t, or zero for the corollary's solver.
Only independent fair bits are preloaded; all random sampling and processing is executed.
Output cells start at the non-Boolean sentinel 2, so every answer needs an actual write. -/

def sumWords (t : ℕ) (I : SumInput) : List ℤ := (t : ℤ) :: I.words

def sumInitial (W t : ℕ) (I : SumInput) (tape : ℕ → Bool) : ℤ → BitVec W :=
  fun a => if (0 : ℤ) ≤ a ∧ ((sumWords t I).length : ℤ) ≤ a ∧
      a < ((sumWords t I).length + I.C.length : ℕ) then 2
    else BddExp3SUM.coinMemory W (sumWords t I) tape a

def SumCorrect (P : List TrulySubcubicAPSP.Instr) (W t fuel : ℕ)
    (I : SumInput) (tape : ℕ → Bool) : Prop :=
  ∃ m, TrulySubcubicAPSP.exec P fuel 0 (sumInitial W t I tape) = some (true, m) ∧
    ∀ j : Fin I.C.length,
      ((m ((sumWords t I).length + j.val : ℕ)).toNat = 0 ∨
       (m ((sumWords t I).length + j.val : ℕ)).toNat = 1) ∧
      ((m ((sumWords t I).length + j.val : ℕ)).toNat = 1 ↔ I.answer (I.C.get j))

def sumCharge (t fuel : ℕ) (I : SumInput) : ℕ :=
  (sumWords t I).length + I.C.length + fuel

def MonteCarloAt (P : List TrulySubcubicAPSP.Instr) (W t fuel : ℕ)
    (K : ℝ) (I : SumInput) : Prop :=
  (∀ tape, ∃ verdict m,
    TrulySubcubicAPSP.exec P fuel 0 (sumInitial W t I tape) = some (verdict, m)) ∧
  MeasurableSet {tape | ¬ SumCorrect P W t fuel I tape} ∧
  BddExp3SUM.coinLaw {tape | ¬ SumCorrect P W t fuel I tape} ≤
    ENNReal.ofReal (K / (max 1 I.N : ℕ)) ∧
  (I.EmptySide → ∀ tape, SumCorrect P W t fuel I tape)

noncomputable def corollaryCost (a b c : ℕ) : ℝ :=
  if a = 0 ∨ b = 0 then (a + b + c + 1 : ℕ)
  else let h := Real.sqrt (a * b : ℕ)
       h ^ (393 / 200 : ℝ) + (a + b : ℕ) * h ^ (899 / 1000 : ℝ) +
         c * h ^ (193 / 200 : ℝ)

noncomputable def reductionCost (P Q : ℕ → ℕ → ℕ → ℝ) (I : SumInput) (t : ℕ) : ℝ :=
  let d := reductionDimension I t
  I.nhat ^ 2 / (d.choose (2 * t) : ℝ) * (P I.N d t + I.N) +
    I.N * I.nhat / (2 : ℝ) ^ t +
    I.C.length * I.nhat / (2 : ℝ) ^ t * (Q I.N d t + 1)

noncomputable def polylogFactor (N e : ℕ) : ℝ := (lg (max 2 N) + 1) ^ e

end SelectedSubset3SUM.Integer


