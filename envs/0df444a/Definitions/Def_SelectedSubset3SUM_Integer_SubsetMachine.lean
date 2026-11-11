-- Prove2me | Definitions.Def_SelectedSubset3SUM_Integer_SubsetMachine
-- name    : SelectedSubset3SUM_Integer_SubsetMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:02.288003+00:00
-- url     : https://prove2.me/theorems/fe815291-7294-4129-b0b4-cabf18c6f12e
-- title:
--   Charged real ring computation and integer subset execution
-- statement:
--   The scalar machine extends the published finite word RAM with an independent scalar memory. Its finite instruction list has exact real constant one, addition, subtraction, multiplication, and direct or indirect scalar memory access, together with the existing word instructions. There are no tests on real scalars, real-to-integer conversions, arbitrary real constants, transforms or convolution instructions. Every executed instruction costs one step.
--
--   Sparse support keys, ranks and cardinalities occupy the word input; arbitrary real weights occupy a separate scalar input. Integer-weight runs use the published word interpreter directly and a packed integer input. A successful run returns the exact convolution value in each query's designated output cell. In both models the total charge is input presentation plus executed instructions plus every query output.
--
--   The deterministic selected-query resource predicates compare this charge with
--
--   $$K(d+1)^e\left(n+\binom d{\le s}+|\mathcal C|\binom{2t}{\ge s}\right).$$
--
--   The real predicate quantifies every real-weight input. The integer predicate additionally quantifies every magnitude exponent $\kappa$ and weights of absolute value at most $\max(2,n)^\kappa$; its word-width requirement includes $d$ and $(\kappa+1)(1+\lfloor\lg\max(2,n)\rfloor)$.
--
--   The conditional solver predicate for Theorem 2.3 instead bounds a single real program by $K(P(n,d,t)+|\mathcal C|Q(n,d,t))$, with nonnegative $P,Q$. No existence or correctness of such a program is built into the machine. Simulating ring arithmetic on the reduction's integer data remains a theorem obligation. These definitions separate actual execution from the resource assertions that solvers must prove.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Problem 2.1, Theorem 2.2 and its algorithm, pp.5–6; footnote 7, p.6; Theorem 2.3, pp.6–8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_SelectedSubset3SUM_Integer_Data

namespace SelectedSubset3SUM.Integer

/-! An exact scalar extension of the published finite word RAM. There are no transforms,
set operations, arbitrary constants, or answer oracles among its instructions. All scalar
and index instructions cost one. Indirect scalar access uses bounded word addresses. -/

inductive ScalarInstr where
  | word (i : TrulySubcubicAPSP.Instr)
  | one (i : ℤ)
  | add (i j k : ℤ)
  | sub (i j k : ℤ)
  | mul (i j k : ℤ)
  | load (i j : ℤ)
  | store (i j : ℤ)

structure ScalarMemory (W : ℕ) where
  words : ℤ → BitVec W
  scalars : ℤ → ℝ

def scalarExec {W : ℕ} (P : List ScalarInstr) :
    ℕ → ℕ → ScalarMemory W → Option (Bool × ScalarMemory W)
  | 0, _, _ => none
  | fuel + 1, pc, m =>
    let next := scalarExec P fuel (pc + 1)
    let writeWord (i : ℤ) (v : BitVec W) :=
      next { m with words := fun a => if a = i then v else m.words a }
    let writeScalar (i : ℤ) (v : ℝ) :=
      next { m with scalars := fun a => if a = i then v else m.scalars a }
    match P.getD pc (.word .reject) with
    | .one i => writeScalar i 1
    | .add i j k => writeScalar i (m.scalars j + m.scalars k)
    | .sub i j k => writeScalar i (m.scalars j - m.scalars k)
    | .mul i j k => writeScalar i (m.scalars j * m.scalars k)
    | .load i j => writeScalar i (m.scalars (m.words j).toInt)
    | .store i j => writeScalar (m.words i).toInt (m.scalars j)
    | .word i =>
      match i with
      | .one i => writeWord i 1
      | .add i j k => writeWord i (m.words j + m.words k)
      | .sub i j k => writeWord i (m.words j - m.words k)
      | .mul i j k => writeWord i (m.words j * m.words k)
      | .load i j => writeWord i (m.words (m.words j).toInt)
      | .store i j => writeWord (m.words i).toInt (m.words j)
      | .bltz i l => scalarExec P fuel (if (m.words i).toInt < 0 then l else pc + 1) m
      | .accept => some (true, m)
      | .reject => some (false, m)

def scalarInitial {d : ℕ} (W n t s : ℕ) (I : RankedData ℝ d) : ScalarMemory W :=
  { words := TrulySubcubicAPSP.loadWords W (rankedKeys n t s I)
    scalars := fun a => if a < 0 then 0 else (rankedScalars I).getD a.toNat 0 }

def RealSubsetRun {d : ℕ} (P : List ScalarInstr) (W n t s fuel : ℕ)
    (I : RankedData ℝ d) : Prop :=
  ∃ m, scalarExec P fuel 0 (scalarInitial W n t s I) = some (true, m) ∧
    ∀ j : Fin I.queries.length,
      m.scalars ((rankedScalars I).length + j.val : ℕ) = convolution I (I.queries.get j)

def realSubsetCharge {d : ℕ} (n t s fuel : ℕ) (I : RankedData ℝ d) : ℕ :=
  (rankedKeys n t s I).length + (rankedScalars I).length + I.queries.length + fuel

def IntegerSubsetRun {d : ℕ} (P : List TrulySubcubicAPSP.Instr)
    (W n t s fuel : ℕ) (I : RankedData ℤ d) : Prop :=
  ∃ m, TrulySubcubicAPSP.exec P fuel 0
      (TrulySubcubicAPSP.loadWords W (rankedIntegers n t s I)) = some (true, m) ∧
    ∀ j : Fin I.queries.length,
      (m ((rankedIntegers n t s I).length + j.val : ℕ)).toInt =
        convolution I (I.queries.get j)

def integerSubsetCharge {d : ℕ} (n t s fuel : ℕ) (I : RankedData ℤ d) : ℕ :=
  (rankedIntegers n t s I).length + I.queries.length + fuel

/-! Input presentation and final scalar/word output materialization are explicit linear
charges in addition to execution. Accessing loaded data inside the algorithm still costs
instructions. These fees do not provide a transform, query answer, sorted list, or dictionary. -/

def RealSelectedBound (P : List ScalarInstr) (b e : ℕ) (K : ℝ) : Prop :=
  ∀ (n d t s : ℕ) (I : RankedData ℝ d), I.Valid n t → s ≤ 2 * t →
    ∀ W ≥ b * (d + Nat.log2 (max 2 n) + 1),
      ∃ fuel, RealSubsetRun P W n t s fuel I ∧
        (realSubsetCharge n t s fuel I : ℝ) ≤
          K * (d + 1 : ℝ) ^ e * subsetCost n d t s I.queries.length

def IntegerSelectedBound (P : List TrulySubcubicAPSP.Instr) (b e : ℕ) (K : ℝ) : Prop :=
  ∀ (κ n d t s : ℕ) (I : RankedData ℤ d),
    I.Valid n t → IntegerWeights I n κ → s ≤ 2 * t →
    ∀ W ≥ b * (d + (κ + 1) * (Nat.log2 (max 2 n) + 1)),
      ∃ fuel, IntegerSubsetRun P W n t s fuel I ∧
        (integerSubsetCharge n t s fuel I : ℝ) ≤
          K * (d + 1 : ℝ) ^ e * subsetCost n d t s I.queries.length

/-! The conditional premise retains all real weights, with an actual uniform ring-arithmetic
solver. Its realization on the integer inputs in the reduction is a proof obligation:
there are no scalar tests or divisions, so ring arithmetic may be simulated modulo a large
enough power of two even when intermediate exact values are huge. Index simulation and
coefficient recovery costs must fit the reduction's polylogarithmic overhead. No such
simulation/correctness theorem is assumed here. The unused cutoff header is zero. -/
def RealSubsetSolver (P Q : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ n d t, 0 ≤ P n d t ∧ 0 ≤ Q n d t) ∧
  ∃ (code : List ScalarInstr) (b : ℕ) (K : ℝ),
    0 < b ∧ 0 < K ∧
    ∀ (n d t : ℕ) (I : RankedData ℝ d), I.Valid n t →
      ∀ W ≥ b * (d + Nat.log2 (max 2 n) + 1),
        ∃ fuel, RealSubsetRun code W n t 0 fuel I ∧
          (realSubsetCharge n t 0 fuel I : ℝ) ≤
            K * (P n d t + I.queries.length * Q n d t)

end SelectedSubset3SUM.Integer


