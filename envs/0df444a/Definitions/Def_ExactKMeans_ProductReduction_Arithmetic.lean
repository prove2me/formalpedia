-- Prove2me | Definitions.Def_ExactKMeans_ProductReduction_Arithmetic
-- name    : ExactKMeans_ProductReduction_Arithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:15:34.87427+00:00
-- url     : https://prove2.me/theorems/a06c9c15-9eb7-4b07-a067-4adf4e9c1742
-- title:
--   Exact arithmetic programs without oracle instructions
-- statement:
--   A finite program has natural address registers and real scalar registers. Instructions are rational constants, copies, natural addition/subtraction/multiplication, real addition/subtraction/multiplication/division, indirect loads and stores, conversion of a natural register to a real register, natural or real comparison branches, jumps, and halt. A configuration includes the program counter and both register memories. One interpreter step executes one instruction. The fuel-bounded interpreter succeeds only upon reaching an explicit halt instruction; missing instructions or exhausted fuel fail.
--
--   The input lists occupy initial registers, with every other register zero. Computing an output within a budget means that the actual interpreter halts using that budget and its initial real registers contain the specified finite output list. There is no arbitrary-function, transcendental-evaluation, optimization or linear-programming instruction. Natural subtraction is truncated and real division is Lean's total division. This is a general arithmetic/comparison model, independent of the graph and selector construction. Source defining real coefficients are supplied as input to programs, rather than computed by an oracle. Complexity clauses quantify one finite program and one polynomial budget before all constructed instances.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed p. 8 (PDF 9), models of computation; pp. 38, 49, 52, 55

import Mathlib

noncomputable section
open scoped Classical

namespace ExactKMeans.ProductReduction

/-- Exact scalar arithmetic/comparison programs, with address registers; no oracle instruction. -/
inductive ArithmeticInstruction where
  | natConst (dst value : ℕ)
  | realConst (dst : ℕ) (value : ℚ)
  | natCopy (dst src : ℕ)
  | realCopy (dst src : ℕ)
  | natAdd (dst lhs rhs : ℕ)
  | natSub (dst lhs rhs : ℕ)
  | natMul (dst lhs rhs : ℕ)
  | realAdd (dst lhs rhs : ℕ)
  | realSub (dst lhs rhs : ℕ)
  | realMul (dst lhs rhs : ℕ)
  | realDiv (dst lhs rhs : ℕ)
  | natLoad (dst address : ℕ)
  | natStore (address src : ℕ)
  | realLoad (dst address : ℕ)
  | realStore (address src : ℕ)
  | natToReal (dst src : ℕ)
  | branchNatLE (lhs rhs yes no : ℕ)
  | branchRealLE (lhs rhs yes no : ℕ)
  | jump (target : ℕ)
  | halt
structure ArithmeticState where
  pc : ℕ
  naturals : ℕ → ℕ
  reals : ℕ → ℝ

def arithmeticStep (s : ArithmeticState) (i : ArithmeticInstruction) : ArithmeticState :=
  let next := { s with pc := s.pc + 1 }
  match i with
  | .natConst d v => {next with naturals := Function.update s.naturals d v}
  | .realConst d v => {next with reals := Function.update s.reals d (v : ℝ)}
  | .natCopy d a => {next with naturals := Function.update s.naturals d (s.naturals a)}
  | .realCopy d a => {next with reals := Function.update s.reals d (s.reals a)}
  | .natAdd d a b => {next with naturals := Function.update s.naturals d (s.naturals a + s.naturals b)}
  | .natSub d a b => {next with naturals := Function.update s.naturals d (s.naturals a - s.naturals b)}
  | .natMul d a b => {next with naturals := Function.update s.naturals d (s.naturals a * s.naturals b)}
  | .realAdd d a b => {next with reals := Function.update s.reals d (s.reals a + s.reals b)}
  | .realSub d a b => {next with reals := Function.update s.reals d (s.reals a - s.reals b)}
  | .realMul d a b => {next with reals := Function.update s.reals d (s.reals a * s.reals b)}
  | .realDiv d a b => {next with reals := Function.update s.reals d (s.reals a / s.reals b)}
  | .natLoad d a => {next with naturals := Function.update s.naturals d (s.naturals (s.naturals a))}
  | .natStore a r => {next with naturals := Function.update s.naturals (s.naturals a) (s.naturals r)}
  | .realLoad d a => {next with reals := Function.update s.reals d (s.reals (s.naturals a))}
  | .realStore a r => {next with reals := Function.update s.reals (s.naturals a) (s.reals r)}
  | .natToReal d a => {next with reals := Function.update s.reals d (s.naturals a : ℝ)}
  | .branchNatLE a b y n => {s with pc := if s.naturals a ≤ s.naturals b then y else n}
  | .branchRealLE a b y n => {s with pc := if s.reals a ≤ s.reals b then y else n}
  | .jump t => {s with pc := t}
  | .halt => s

def arithmeticRun (code : List ArithmeticInstruction) : ℕ → ArithmeticState → Option ArithmeticState
  | 0, _ => none
  | fuel + 1, s => match code[s.pc]? with
    | none => none
    | some .halt => some s
    | some i => arithmeticRun code fuel (arithmeticStep s i)

def ArithmeticComputes (code : List ArithmeticInstruction) (ns : List ℕ) (rs output : List ℝ)
    (budget : ℕ) : Prop :=
  ∃ s, arithmeticRun code budget
    {pc := 0, naturals := fun i => ns[i]?.getD 0, reals := fun i => rs[i]?.getD 0} = some s ∧
    ∀ i : Fin output.length, s.reals i.val = output[i]
end ExactKMeans.ProductReduction


