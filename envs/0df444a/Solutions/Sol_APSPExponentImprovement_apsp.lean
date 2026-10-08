-- Prove2me | solution 1 for APSPExponentImprovement.apsp
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T16:50:17.507992+00:00
-- url     : https://prove2.me/submissions/385d2270-20cc-414f-9acc-e6b1a02311db

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_Problems
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_APSPExponentImprovement_minPlusComposable
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async true
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Transport from the original paper's word RAM and problem statements to the
mission's separately declared copies. No algorithm or running-time result is
assumed here: every theorem below preserves the source proof's exact step bound.
-/

namespace APSPProofBridge

/-- The instruction correspondence preserves each operand and branch target. -/
def instruction : EndStatement.Instr → TrulySubcubicAPSP.Instr
  | .one i => .one i
  | .add i j k => .add i j k
  | .sub i j k => .sub i j k
  | .mul i j k => .mul i j k
  | .load i j => .load i j
  | .store i j => .store i j
  | .bltz i l => .bltz i l
  | .accept => .accept
  | .reject => .reject

/-- Map every instruction, preserving program length and every program position. -/
def program (P : List EndStatement.Instr) : List TrulySubcubicAPSP.Instr :=
  P.map instruction

theorem loadWords (W : Nat) (ws : List Int) :
    TrulySubcubicAPSP.loadWords W ws = EndStatement.loadWords W ws := rfl

theorem instructionAt (P : List EndStatement.Instr) (pc : Nat) :
    (program P).getD pc .reject = instruction (P.getD pc .reject) := by
  induction P generalizing pc with
  | nil => simp [program, instruction]
  | cons i P ih =>
    cases pc with
    | zero => simp [program]
    | succ pc => simpa [program] using ih pc

/-- The copied machine executes the mapped program identically, at every word
width, time bound, program counter, and initial memory. -/
theorem exec {W : Nat} (P : List EndStatement.Instr) (t pc : Nat)
    (m : Int → BitVec W) :
    TrulySubcubicAPSP.exec (program P) t pc m = EndStatement.exec P t pc m := by
  induction t generalizing pc m with
  | zero => rfl
  | succ t ih =>
    simp only [TrulySubcubicAPSP.exec, EndStatement.exec, instructionAt]
    cases P.getD pc .reject <;> simp only [instruction] <;> try rfl
    all_goals apply ih

/-- Instance conversion together with matching input, verdict, and output
specifications suffices to transport an execution witness. -/
theorem solvedBy {Q : EndStatement.Problem} {R : TrulySubcubicAPSP.Problem}
    (f : ∀ {n : Nat}, R.Instance n → Q.Instance n)
    (input_eq : ∀ {n : Nat} (x : R.Instance n), Q.input (f x) = R.input x)
    (yes_iff : ∀ {n : Nat} (x : R.Instance n), Q.yes (f x) ↔ R.yes x)
    (output_iff : ∀ {n : Nat} (x : R.Instance n) (out : Nat → Int),
      Q.output (f x) out ↔ R.output x out)
    {n : Nat} (x : R.Instance n) (P : List EndStatement.Instr) (W t : Nat)
    (h : Q.SolvedBy (f x) P W t) : R.SolvedBy x (program P) W t := by
  obtain ⟨verdict, m, run, correct, output⟩ := h
  refine ⟨verdict, m, ?_, correct.trans (yes_iff x), ?_⟩
  · rw [exec, loadWords, ← input_eq x]
    exact run
  · apply (output_iff x _).mp
    simpa only [input_eq x] using output

/-- Transport preserves the program's step bound, width bound, exponent, and all
quantifiers over input magnitudes, sizes, instances, and word widths. -/
theorem solvedInTime {Q : EndStatement.Problem} {R : TrulySubcubicAPSP.Problem}
    (f : ∀ {n : Nat}, R.Instance n → Q.Instance n)
    (input_eq : ∀ {n : Nat} (x : R.Instance n), Q.input (f x) = R.input x)
    (yes_iff : ∀ {n : Nat} (x : R.Instance n), Q.yes (f x) ↔ R.yes x)
    (output_iff : ∀ {n : Nat} (x : R.Instance n) (out : Nat → Int),
      Q.output (f x) out ↔ R.output x out)
    {r : Rat} (h : Q.SolvedInTime r) : R.SolvedInTime r := by
  intro κ
  obtain ⟨P, b, T, bound, correct⟩ := h κ
  refine ⟨program P, b, T, bound, ?_⟩
  intro n x magnitude W width
  apply solvedBy f input_eq yes_iff output_iff
  apply correct n (f x) _ W width
  simpa only [input_eq x] using magnitude















/-- Every original path is a mission path of the same weight and endpoints. -/
theorem pathToMission {n : Nat} {w : Fin n → Fin n → Option Int}
    {i j : Fin n} {d : Int} (h : EndStatement.Path w i j d) :
    TrulySubcubicAPSP.Path w i j d := by
  induction h with
  | nil i => exact .nil i
  | cons edge _ ih => exact .cons edge ih

/-- Every mission path is an original path of the same weight and endpoints. -/
theorem pathToOriginal {n : Nat} {w : Fin n → Fin n → Option Int}
    {i j : Fin n} {d : Int} (h : TrulySubcubicAPSP.Path w i j d) :
    EndStatement.Path w i j d := by
  induction h with
  | nil i => exact .nil i
  | cons edge _ ih => exact .cons edge ih

theorem path_iff {n : Nat} {w : Fin n → Fin n → Option Int}
    {i j : Fin n} {d : Int} :
    EndStatement.Path w i j d ↔ TrulySubcubicAPSP.Path w i j d :=
  ⟨pathToMission, pathToOriginal⟩

/-- Change only the proof of the no-negative-cycle promise. -/
def apspInstance {n : Nat} (x : TrulySubcubicAPSP.APSP.Instance n) :
    EndStatement.APSP.Instance n :=
  ⟨x.val, fun i d h => x.property i d (pathToMission h)⟩

theorem apspOutput {n : Nat} (x : TrulySubcubicAPSP.APSP.Instance n)
    (out : Nat → Int) :
    EndStatement.APSP.output (apspInstance x) out ↔
      TrulySubcubicAPSP.APSP.output x out := by
  simp only [EndStatement.APSP, TrulySubcubicAPSP.APSP, apspInstance, path_iff]

/-- APSP transport includes the graph promise, reachability flags, attained
minimum distances, and unreachable pairs. -/
theorem apsp {r : Rat} (h : EndStatement.APSP.SolvedInTime r) :
    TrulySubcubicAPSP.APSP.SolvedInTime r :=
  solvedInTime apspInstance (fun _ => rfl) (fun _ => Iff.rfl) apspOutput h

end APSPProofBridge

end

section


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9

























/-- `1 / 2 ≤ log x` for `x ≥ 2`. -/
theorem one_half_le_log_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ log x :=
  one_half_lt_log_two.le.trans (log_le_log two_pos hx)














/-! ### The rounded logarithm `Nat.clog` -/

/-- `⌈log_b n⌉ < log_b n + 1`, for all natural numbers `b` and `n` (for `b ≤ 1` or `n = 0` both
logarithms are `0`). -/
theorem natCast_clog_lt_logb_add_one (b n : ℕ) : (Nat.clog b n : ℝ) < logb b n + 1 := by
  rw [← natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (div_nonneg (log_natCast_nonneg n) (log_natCast_nonneg b))














end Real

namespace ThreeSumApsp






end ThreeSumApsp

end
end

section


/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩





/-- A bound with a constant of unknown sign, when `g` is nonnegative on the domain. -/
theorem of_exists_const (hfg : ∃ C : ℝ, ∀ x, dom x → f x ≤ C * g x) (hg : ∀ x, dom x → 0 ≤ g x) :
    Dominated dom f g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨|C|, abs_nonneg C, fun x hx =>
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hg x hx))⟩
















/-! ### Leaving the calculus -/











/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC

/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩














/-- Substituting the parameters: a bound in `x` gives a bound in `y` at `x = φ y`, on every domain
that `φ` maps into `dom`. -/
protected theorem comp (hfg : Dominated dom f g) (φ : β → α) {dom' : β → Prop}
    (hφ : ∀ y, dom' y → dom (φ y)) : Dominated dom' (fun y => f (φ y)) fun y => g (φ y) := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun y hy => hf (φ y) (hφ y hy)⟩

/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)






















/-! ### Products and quotients -/














/-- A constant factor of any sign in front of a function that is nonnegative on the domain is
absorbed. -/
theorem const_mul_of_nonneg (hfg : Dominated dom f g) (c : ℝ) (hf : ∀ x, dom x → 0 ≤ f x) :
    Dominated dom (fun x => c * f x) g :=
  (of_exists_const ⟨c, fun _ _ => le_rfl⟩ hf).trans hfg





































/-! ### Functions of one natural number -/






















/-- A bound by a nonnegative `g` that holds from some unknown point on gives a bound by `g + 1`
everywhere. -/
theorem of_eventually_add_one {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n)
    (hg : ∀ n, 0 ≤ g n) : Dominated (fun _ => True) f fun n => g n + 1 := by
  have hpos : ∀ n, 0 ≤ n → 0 < g n + 1 := fun n _ => add_pos_of_nonneg_of_pos (hg n) zero_lt_one
  refine (of_eventually (C := |C|) (hfg.mono fun n hn => hn.trans ?_) hpos).mono_dom
    fun n _ => n.zero_le
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (hg n)).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg C))









end Dominated












end ThreeSumApsp

end
end

section


/-!
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- A bound `|f n| ≤ C * g n` from some `n₀` on gives `f = O(g)`. -/
theorem isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  refine IsBigO.of_bound |C| (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  exact (h n hn).trans (le_abs_self _)










/-- `n ^ a = O(n ^ b)` for `a ≤ b`. -/
theorem isBigO_rpow_rpow_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine isBigO_of_abs_le 1 1 fun n hn => ?_
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hab

/-- `n ^ a * n ^ b = n ^ (a + b)` for all large `n`. -/
theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]

/-- `(log n) ^ e = o(n ^ η)` for `η > 0`. -/
theorem isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop (e : ℝ) hη).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h

/-- `(log n) ^ e = O((log n) ^ e')` for `e ≤ e'`. -/
theorem isBigO_log_pow_log_pow_of_le {e e' : ℕ} (he : e ≤ e') :
    (fun n : ℕ => Real.log n ^ e) =O[atTop] fun n : ℕ => Real.log n ^ e' := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlog
  refine isBigO_of_abs_le 1 n₀ fun n hn => ?_
  rw [one_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans (hn₀ n hn)) e)]
  exact pow_le_pow_right₀ (hn₀ n hn) he

/-- `n ^ a * (log n) ^ e = O(n ^ b * (log n) ^ e')` for `a ≤ b` and `e ≤ e'`. -/
theorem isBigO_rpow_mul_log_pow_of_le {a b : ℝ} {e e' : ℕ} (hab : a ≤ b) (he : e ≤ e') :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b * Real.log n ^ e' :=
  (isBigO_rpow_rpow_of_le hab).mul (isBigO_log_pow_log_pow_of_le he)

/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`. -/
theorem isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)






/-- Constants are absorbed as well: `C * (n ^ a * (log n) ^ e) ≤ n ^ b` for all large `n`, if
`a < b`. -/
theorem eventually_mul_rpow_mul_log_pow_le (C : ℝ) {a b : ℝ} (hab : a < b) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ a * Real.log n ^ e) ≤ (n : ℝ) ^ b := by
  have h := ((isLittleO_rpow_mul_log_pow_rpow hab e).const_mul_left C).def zero_lt_one
  filter_upwards [h] with n hn
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg b)] at hn
  exact (le_abs_self _).trans hn






end ThreeSumApsp

end
end

section


/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/

/-- `n ^ a = O(n^a)`. -/
theorem isBigOPow_rpow (a : ℝ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ a) a :=
  isBigO_refl _ _

/-- `n ^ k = O(n^k)` for a natural number `k`. -/
theorem isBigOPow_natCast_pow (k : ℕ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ k) k := by
  simpa only [Real.rpow_natCast] using isBigOPow_rpow (k : ℝ)





/-- A constant is `O(n^0)`. -/
theorem isBigOPow_const (c : ℝ) : IsBigOPow (fun _ => c) 0 :=
  isBigO_of_abs_le |c| 0 fun n _ => by rw [Real.rpow_zero, mul_one]

namespace IsBigOPow



























































/-- `O(n^a) ⊆ Õ(n^a)`. -/
theorem isPowPolylog (hf : IsBigOPow f a) : IsPowPolylog f a :=
  ⟨0, by simpa only [pow_zero, mul_one, IsBigOPow] using hf⟩

end IsBigOPow








































/-! ### `Õ(n^a)` -/

/-- `n ^ a * (log n) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) a :=
  ⟨e, isBigO_refl _ _⟩










/-- `(log n) ^ e = Õ(1)`. -/
theorem isPowPolylog_log_pow (e : ℕ) : IsPowPolylog (fun n : ℕ => Real.log n ^ e) 0 :=
  ⟨e, by simpa only [Real.rpow_zero, one_mul] using isBigO_refl (fun n : ℕ => Real.log n ^ e) atTop⟩

/-- `log n = Õ(1)`. -/
theorem isPowPolylog_log : IsPowPolylog (fun n : ℕ => Real.log n) 0 := by
  simpa only [pow_one] using isPowPolylog_log_pow 1

/-- A constant is `Õ(1)`. -/
theorem isPowPolylog_const (c : ℝ) : IsPowPolylog (fun _ => c) 0 :=
  (isBigOPow_const c).isPowPolylog

namespace IsPowPolylog






/-- If `g = Õ(n^a)` and `f = O(g)`, then `f = Õ(n^a)`. -/
theorem of_isBigO (hg : IsPowPolylog g a) (hfg : f =O[atTop] g) : IsPowPolylog f a := by
  obtain ⟨e, hg⟩ := hg
  exact ⟨e, hfg.trans hg⟩

/-- If `|f n| ≤ |g n|` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left (hg : IsPowPolylog g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsPowPolylog f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left_of_nonneg (hg : IsPowPolylog g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsPowPolylog f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

/-- The exponent may be raised. -/
protected theorem mono (hf : IsPowPolylog f a) (hab : a ≤ b) : IsPowPolylog f b := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.trans (isBigO_rpow_mul_log_pow_of_le hab le_rfl)⟩

/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`. -/
protected theorem add (hf : IsPowPolylog f a) (hg : IsPowPolylog g a) :
    IsPowPolylog (fun n => f n + g n) a := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  exact ⟨max e₁ e₂, (hf.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_left _ _))).add
    (hg.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_right _ _)))⟩

/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => c * f n) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.const_mul_left c⟩





/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`. -/
protected theorem mul (hf : IsPowPolylog f a) (hg : IsPowPolylog g b) :
    IsPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  refine ⟨e₁ + e₂, (hf.mul hg).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [rpow_mul_rpow_eventuallyEq a b] with n hn
  rw [← hn, pow_add, mul_mul_mul_comm]


























/-- If `f = Õ(n^a)` then `|f| = Õ(n^a)`. -/
protected theorem abs (hf : IsPowPolylog f a) : IsPowPolylog (fun n => |f n|) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.norm_left⟩

/-- If `f = Õ(n^a)` and `g n = f n` for all large `n`, then `g = Õ(n^a)`. -/
protected theorem congr (hf : IsPowPolylog f a) (h : f =ᶠ[atTop] g) : IsPowPolylog g a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.congr' h EventuallyEq.rfl⟩












end IsPowPolylog












































/-- `log (c * n ^ κ) = Õ(1)`. -/
theorem isPowPolylog_log_mul_rpow (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * (n : ℝ) ^ κ)) 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa only [zero_mul, Real.log_zero] using isPowPolylog_const 0
  · refine ((isPowPolylog_const (Real.log c)).add (isPowPolylog_log.const_mul κ)).congr ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [Real.log_mul hc (Real.rpow_pos_of_pos hpos κ).ne', Real.log_rpow hpos]

end ThreeSumApsp

end
end

section


/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp















variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/








namespace UpperBigOPow






end UpperBigOPow

/-! ### `Õ(n^a)` from above -/

/-- `f = Õ(n^a)` is in particular an upper bound on `f`. -/
theorem IsPowPolylog.upperPowPolylog (hf : IsPowPolylog f a) : UpperPowPolylog f a := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨C, e, hC.mono fun n hn => ?_⟩
  have hnonneg : 0 ≤ (n : ℝ) ^ a * Real.log n ^ e :=
    mul_nonneg (Real.rpow_nonneg n.cast_nonneg a) (pow_nonneg (Real.log_natCast_nonneg n) e)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  exact (le_abs_self _).trans hn

namespace UpperPowPolylog

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperPowPolylog f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowPolylog f' a := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨C, e, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩

/-- An upper bound `Õ(n^a)` is a bound by a nonnegative function of the class `Õ(n^a)`. -/
theorem exists_isPowPolylog (h : UpperPowPolylog f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowPolylog g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨fun n => |C * ((n : ℝ) ^ a * Real.log n ^ e)|, fun n => abs_nonneg _,
    ((isPowPolylog_rpow_mul_log_pow a e).const_mul C).abs,
    hC.mono fun n hn => hn.trans (le_abs_self _)⟩

/-- For a function that is eventually nonnegative, the bound on `f` is a bound on `|f|`. -/
theorem isPowPolylog (h : UpperPowPolylog f a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n) :
    IsPowPolylog f a := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact hg.mono_left_of_nonneg h0 hfg






/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`, from above. -/
protected theorem add (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g a) :
    UpperPowPolylog (fun n => f n + g n) a := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  obtain ⟨G, -, hG, hgG⟩ := hg.exists_isPowPolylog
  exact (hF.add hG).upperPowPolylog.mono_left
    ((hfF.and hgG).mono fun n hn => add_le_add hn.1 hn.2)








/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`, from above, if the second factor is eventually nonnegative. -/
protected theorem mul (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g b)
    (hg0 : ∀ᶠ n in atTop, 0 ≤ g n) :
    UpperPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  exact (hF.mul (hg.isPowPolylog hg0)).upperPowPolylog.mono_left
    ((hfF.and hg0).mono fun n hn => mul_le_mul_of_nonneg_right hn.1 hn.2)






end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/






namespace UpperPowLittleO




















end UpperPowLittleO

end ThreeSumApsp

end
end

section


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/








































/-! ## Configurations and single steps -/






















/-! ## Runs -/




























/-- Within no steps there is no verdict. -/
theorem exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]

private theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  rw [exec, step]
  cases P.getD c.pc .reject <;> rfl

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by rw [exec_succ, h]













/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => rwa [exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/





































/-! ## Straight-line code -/





















































/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

















































end known

/-! ## Branches and verdicts -/























/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}






















































end framing

end ThreeSumApsp.WordRam

end
end

section


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/




























/-- `EndStatement.Problem.SolvedBy` counts the output cells as `1 + len + i`, and `output` counts
them as `(len + 1) + i`. -/
theorem output_cons {W : ℕ} (c : ℤ → BitVec W) (n : ℤ) (l : List ℤ) :
    (fun i : ℕ => (c ((1 + l.length + i : ℕ) : ℤ)).toInt) = output c (n :: l).length := by
  funext i
  simp only [output, List.length_cons, Nat.add_comm 1]
  rfl

/-- `SolvesWithin` is `Solves` for the problem `ofEnd Q`, on the instances with `U = n^κ`. -/
theorem solvesWithin_iff {Q : EndStatement.Problem} {κ : ℕ} {P : List Instr} {b : ℕ} {T : ℕ → ℝ} :
    SolvesWithin Q κ P b T ↔ Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) fun x => T x.n := by
  constructor
  · intro h x hx bits hbits
    obtain ⟨t, ht, verdict, m, hexec, hyes, hout⟩ :=
      h x.n x.x (hx ▸ x.bounded) bits (by simpa [Admissible] using hbits)
    exact ⟨t, verdict, m, ht, hexec, hyes, output_cons m x.n (Q.input x.x) ▸ hout⟩
  · intro h n x hx W hW
    obtain ⟨t, verdict, c, ht, hrun, hyes, hout⟩ :=
      h ⟨n, n ^ κ, x, hx⟩ rfl W (by simpa [Admissible] using hW)
    exact ⟨t, ht, verdict, c, hrun, hyes, (output_cons c n (Q.input x)).symm ▸ hout⟩

/-- `SolvedInTimeAt` in terms of `Solves`. -/
theorem solvedInTimeAt_iff {Q : EndStatement.Problem} {κ : ℕ} {a : ℝ} {e : ℕ} :
    SolvedInTimeAt Q κ a e ↔ ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ)
        fun x => C * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1) := by
  simp only [SolvedInTimeAt, solvesWithin_iff]

/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : Problem} {P : List Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : _root_.ThreeSumApsp.WordRam.Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : _root_.ThreeSumApsp.WordRam.Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩



















/-! ## Bounds up to a constant -/

/-- A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. -/
theorem exists_solves_of_dominated {prob : Problem} {dom dom' : prob.Inst → Prop}
    {f f' : prob.Inst → ℝ}
    (h : ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom fun x => C * f x)
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity) :
    ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom' fun x => C * f' x := by
  obtain ⟨P, b, C, h⟩ := h
  obtain ⟨K, -, hf⟩ := hf.const_mul_of_nonneg C hf0
  exact ⟨P, b, K, h.mono le_rfl hdom hf⟩






















/-! ## Bounds in one size -/

/-- The bound `O(n^a (log n)^e)` may be replaced by a bound `O(n^a' (log n)^e')` that is at least as
large, up to a constant, for all large `n`. -/
theorem SolvedInTimeAt.of_eventually_le {Q : EndStatement.Problem} {κ : ℕ} {a a' C : ℝ} {e e' : ℕ}
    (h : SolvedInTimeAt Q κ a e)
    (hle : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a * Real.log n ^ e ≤ C * ((n : ℝ) ^ a' * Real.log n ^ e')) :
    SolvedInTimeAt Q κ a' e' := by
  have hall : Dominated (fun _ : ℕ => True) (fun n => (n : ℝ) ^ a * Real.log n ^ e + 1)
      fun n => (n : ℝ) ^ a' * Real.log n ^ e' + 1 :=
    (Dominated.of_eventually_add_one hle fun n => by positivity).add
      (.of_le fun n _ => le_add_of_nonneg_left (by positivity))
  exact solvedInTimeAt_iff.2 (exists_solves_of_dominated (solvedInTimeAt_iff.1 h) (fun _ hx => hx)
    (hall.comp (fun x : Bounded Q => x.n) fun _ _ => trivial))













/-- A bound `O(n^a (log n)^{O(1)})` is a bound `O(n^a')` for `a < a'`. -/
theorem SolvedInPolylogTime.solvedInTime {Q : EndStatement.Problem} {a a' : ℝ}
    (h : SolvedInPolylogTime Q a) (ha : a < a') : SolvedInTime Q a' 0 := fun κ =>
  let ⟨e, he⟩ := h κ
  he.of_eventually_le (C := 1) <| by
    simpa only [one_mul, pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le 1 ha e

end ThreeSumApsp.WordRam

end
end

section


/-!
# APSP: from a solver of the task to a program for the layout of the end statement

APSP (Theorem 22).  `realized_apsp`: if the task `apTask` is solved in time T, then
`EndStatement.APSP` is solved on the word RAM within a constant times T.

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n².  The
answer goes to the 2n² cells from 1 + 2n², and the free pointer is 1 + 4n² (`apspInst`).  The task
speaks of the graph with weights in `WithTop ℤ` that is read from the two lists, which is the graph
of the instance (`graphOf_apsp`).  So the input meets the task's precondition (`pre_apsp`), and what
a solver leaves in the output cells is what `EndStatement.APSP` asks for (`post_apsp`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec































































































/-- **APSP**: if the task is solved in time T, then APSP is solved on the word RAM within a constant
times T. -/
theorem realized_apsp (T : ℕ → ℝ → ℝ) (h : SolvedIn apTask T) :
    Realized EndStatement.APSP T :=
  wrapApsp.realized h

end Light.Sec3

end
end

section


/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/




















































/-! ## Bounds in one size, for all large sizes -/


































/-- A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for
every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInPolylogTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by
  intro κ
  obtain ⟨T, hT, C, e, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact ⟨e, solvedAt_of_realized T κ (hR T hT) hb⟩






















end ThreeSumApsp.FromClaims

end
end

section


/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam






























/-- The rounded bound is `O(n^r)` in the sense of the end statement. -/
theorem bigO_stepBound (C : ℝ) {r : ℚ} (hr0 : 0 ≤ r) : EndStatement.BigO (stepBound C r) r := by
  refine bigO_of_le_rpow (C := 2 * |C| + 1) hr0 fun n hn => ?_
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hr0)
  have habs : C * ((n : ℝ) ^ (r : ℝ) + 1) ≤ |C| * ((n : ℝ) ^ (r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hceil : (stepBound C r n : ℝ) < |C| * ((n : ℝ) ^ (r : ℝ) + 1) + 1 :=
    (Nat.cast_le.2 (Nat.ceil_le_ceil habs)).trans_lt (Nat.ceil_lt_add_one (by positivity))
  -- `|C| (X + 1) + 1 ≤ (2 |C| + 1) X` for `X ≥ 1`
  nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.2 hone)]

/-- **A bound `O(n^a)` of an item statement, with `a` the rational `r`, is the bound `O(n^r)` of the
end statement**, with the same program and the same slope. -/
theorem SolvedInTime.endStatement {Q : EndStatement.Problem} {a : ℝ} (h : SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by
  subst hr
  intro κ
  obtain ⟨P, b, C, hsolves⟩ := h κ
  refine ⟨P, b, stepBound C r, bigO_stepBound C hr0, fun n x hx W hW => ?_⟩
  obtain ⟨t, ht, verdict, c, hrun, hanswer⟩ := hsolves n x hx W hW
  have ht' : t ≤ stepBound C r n := by
    simp only [pow_zero, mul_one] at ht
    exact_mod_cast ht.trans (Nat.le_ceil _)
  exact ⟨verdict, c, WordRam.exec_mono (c := ⟨0, _⟩) hrun ht', hanswer⟩

end ThreeSumApsp.WordRam

end
end

section


/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/




































/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/







/-- `⌈log_b n⌉ + 1 = O(log n)` on `n ≥ 2`, for every natural number `b`. -/
theorem dominated_clog_add_one_log (b : ℕ) :
    Dominated (fun n : ℕ => 2 ≤ n) (fun n => (Nat.clog b n : ℝ) + 1) fun n => log n := by
  have hlogb : 0 ≤ log b := log_natCast_nonneg b
  refine .of_le_const_mul (C := 1 / log b + 4) (by positivity) fun n hn => ?_
  have hhalf : 1 / 2 ≤ log n := one_half_le_log_of_two_le (by exact_mod_cast hn)
  have hclog := natCast_clog_lt_logb_add_one b n
  rw [add_mul, one_div_mul_eq_div]
  -- `⌈log_b n⌉ + 1 < log n / log b + 2` and `2 ≤ 4 log n`
  rw [logb] at hclog
  linarith [hclog, hhalf]

end ThreeSumApsp

end
end

section


/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)




































/-! ## `logU` of a multiple -/
























/-! ## `logU` along bounds that are polynomial in `n` -/

/-- `log u(n) = Õ(1)` for bounds `1 ≤ u(n) ≤ c n^κ` on the numbers. -/
theorem isPowPolylog_logU_of_le {mag : ℕ → ℝ} {c κ : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => logU (mag n)) 0 := by
  refine (isPowPolylog_log_mul_rpow (2 * c) κ).mono_left_of_nonneg
    (.of_forall fun n => (logU_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨hone, hle⟩ := h n hn
  refine Real.log_le_log (lt_max_of_lt_right two_pos) (max_le ?_ ?_) <;> rw [mul_assoc] <;> linarith

/-- `log (c n^κ) = Õ(1)`. -/
theorem isPowPolylog_logU_mul_rpow {c κ : ℝ} (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    IsPowPolylog (fun n : ℕ => logU (c * (n : ℝ) ^ κ)) 0 :=
  isPowPolylog_logU_of_le fun _ hn =>
    ⟨one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ), le_rfl⟩

end ThreeSumApsp

end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The new min-plus solver is an explicit hypothesis throughout this file. The
repeated-squaring algorithm, layout compiler, and source-to-mission transport
are existing proved algorithms. No improved min-plus algorithm is assumed as
an axiom or hidden in a definition.
-/

namespace Improvement.APSP

open ThreeSumApsp ThreeSumApsp.WordRam

/-- A composable min-plus algorithm with the same exponent at every polynomial
weight bound, including a constant multiplier. A solver can depend on the bound.
The conclusion `M.minPlusProduct T` still certifies all its legal inputs. -/
def MinPlusAtScaledPowers (M : DetTimeModel) (a : ℝ) : Prop :=
  ∀ c : ℝ, 1 ≤ c → ∀ κ : ℝ, 0 ≤ κ →
    ∃ T : ℕ → ℝ → ℝ, M.minPlusProduct T ∧
      UpperPowPolylog (fun n => T n (c * (n : ℝ) ^ κ)) a

/-- Repeated squaring uses only a polylogarithmic number of products. -/
theorem rounds_polylog :
    IsPowPolylog (fun n : ℕ => (Nat.clog 2 n : ℝ) + 1) 0 := by
  obtain ⟨C, _hC, hC⟩ := dominated_clog_add_one_log 2
  exact (isPowPolylog_log.const_mul C).mono_left_of_nonneg
    (.of_forall fun n => by positivity)
    (Filter.eventually_atTop.2 ⟨2, hC⟩)

/-- APSP retains the full min-plus exponent. The `n²` matrix-writing overhead
fits whenever the exponent is at least two. -/
theorem apsp_polylog_of_minPlus {M : DetTimeModel} {a : ℝ}
    (ha : 2 ≤ a) (hsq : Claim.ApspFromMinPlus M)
    (hmp : MinPlusAtScaledPowers M a) : Claim.ApspInPolylog M a := by
  obtain ⟨c, C, hc, hsq⟩ := hsq
  intro κ hκ
  obtain ⟨T, hT, hb⟩ := hmp c hc (κ + 1) (by linarith)
  refine ⟨_, hsq T hT, ?_⟩
  have hwrite : IsPowPolylog
      (fun n : ℕ => C * ((n : ℝ) ^ 2 * (1 + logU (c * (n : ℝ) ^ (κ + 1))))) a := by
    have h := ((isBigOPow_natCast_pow 2).isPowPolylog.mul
      ((isPowPolylog_const 1).add
        (isPowPolylog_logU_mul_rpow hc (by linarith : 0 ≤ κ + 1)))).const_mul C
    exact (by simpa using h : IsPowPolylog _ 2).mono ha
  have htotal := (hb.add hwrite.upperPowPolylog).mul rounds_polylog.upperPowPolylog
    (.of_forall fun n => by positivity)
  refine (by simpa only [add_zero] using htotal : UpperPowPolylog _ a).mono_left ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hpow : (n : ℝ) * (n : ℝ) ^ κ = (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one (Nat.cast_pos.2 hn).ne', mul_comm]
  simp only [hpow, mul_comm]
  exact le_rfl

/-- A stronger Light min-plus solver is sufficient for the source APSP bound,
with no factor-of-three loss in its exponent saving. -/
theorem source_apsp_polylog {a : ℝ} (ha : 2 ≤ a)
    (hmp : MinPlusAtScaledPowers Light.lightModel a) :
    SolvedInPolylogTime EndStatement.APSP a :=
  FromClaims.solvedInPolylogTime_of_claim Light.Sec3.realized_apsp
    (apsp_polylog_of_minPlus ha Light.Sec3.claim_apspFromMinPlus hmp)

/-- Strict exponent slack absorbs all fixed powers of the logarithm, and the
existing bridge preserves the actual machine execution and output contract. -/
theorem mission_apsp_of_minPlus {a : ℝ} {r : ℚ}
    (ha : 2 ≤ a) (har : a < (r : ℝ))
    (hmp : MinPlusAtScaledPowers Light.lightModel a) :
    TrulySubcubicAPSP.APSP.SolvedInTime r := by
  have hr : 0 ≤ r := by exact_mod_cast (show (0 : ℝ) ≤ r by linarith)
  exact APSPProofBridge.apsp
    (((source_apsp_polylog ha hmp).solvedInTime har).endStatement rfl hr)










end Improvement.APSP





end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Improvement.APSP

open ThreeSumApsp

/-- A Light solver can be bounded using any larger magnitude argument. This
changes its time bound, not its program or its resource requirements. -/
theorem solvedIn_raiseMagnitude {task : Light.Task} {T : ℕ → ℝ → ℝ}
    (h : Light.SolvedIn task T) (v : ℕ → ℝ) :
    Light.SolvedIn task (fun n u => T n (max u (v n))) := by
  obtain ⟨P, p, Tn, need, hn, hs, ht⟩ := h
  exact ⟨P, p, Tn, need, hn, hs, fun n U u hn hU hu =>
    ht n U _ hn hU (hu.trans (le_max_left _ _))⟩

/-- The existing source-level min-plus claim is already sufficiently uniform.
For `c n^κ`, use its solver at exponent `κ+1`; eventually `c ≤ n`. No
monotonicity assumption on the originally advertised time function is needed. -/
theorem scaledPowers_of_minPlusInPolylog {a : ℝ}
    (h : Claim.MinPlusInPolylog Light.lightModel a) :
    MinPlusAtScaledPowers Light.lightModel a := by
  intro c _hc κ hκ
  obtain ⟨T, hT, hb⟩ := h (κ + 1) (by linarith)
  refine ⟨fun n u => T n (max u ((n : ℝ) ^ (κ + 1))),
    solvedIn_raiseMagnitude hT (fun n => (n : ℝ) ^ (κ + 1)), hb.mono_left ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (⌈c⌉₊ + 1)] with n hn
  have hn1 : 1 ≤ n := by omega
  have hcn : c ≤ (n : ℝ) :=
    (Nat.le_ceil c).trans (Nat.cast_le.2 (by omega : ⌈c⌉₊ ≤ n))
  have hmag : c * (n : ℝ) ^ κ ≤ (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one (Nat.cast_pos.2 hn1).ne', mul_comm]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hcn (Real.rpow_nonneg n.cast_nonneg κ)
  rw [max_eq_right hmag]

/-- Repeated squaring can consume the existing source-level min-plus claim
without strengthening its magnitude quantifiers. -/
theorem mission_apsp_of_minPlusInPolylog {a : ℝ} {r : ℚ}
    (ha : 2 ≤ a) (har : a < (r : ℝ))
    (h : Claim.MinPlusInPolylog Light.lightModel a) :
    TrulySubcubicAPSP.APSP.SolvedInTime r :=
  mission_apsp_of_minPlus ha har (scaledPowers_of_minPlusInPolylog h)

/-- Concrete final reduction for the planned improved min-plus source claim. -/
theorem mission_apsp_29983_of_minPlusInPolylog
    (h : Claim.MinPlusInPolylog Light.lightModel 2.99825) :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.9983 :=
  mission_apsp_of_minPlusInPolylog (by norm_num) (by norm_num) h












































end Improvement.APSP






end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Repeated squaring retains the composable min-plus exponent; the positive
gap to 2.9983 absorbs the fixed logarithmic factors. -/
theorem APSPExponentImprovement.apsp_sourceProof :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.9983 :=
  Improvement.APSP.mission_apsp_29983_of_minPlusInPolylog
    APSPExponentImprovement.minPlusComposable



end


theorem solution : TrulySubcubicAPSP.APSP.SolvedInTime
  (@OfScientific.ofScientific.{0} Rat Rat.instOfScientific (nat_lit 29983) Bool.true (nat_lit 4)) := by
  exact @APSPExponentImprovement.apsp_sourceProof

#print axioms solution
