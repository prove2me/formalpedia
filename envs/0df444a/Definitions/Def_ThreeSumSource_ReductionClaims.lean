-- Prove2me | Definitions.Def_ThreeSumSource_ReductionClaims
-- name    : ThreeSumSource_ReductionClaims
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-06T15:24:03.359382+00:00
-- url     : https://prove2.me/theorems/2e38e764-4481-4bd9-9100-9f2ad922e0c8
-- title:
--   Running-time interfaces for the deterministic 3SUM reductions
-- statement:
--   The source interfaces for reducing integer 3SUM to Convolution-3SUM and Convolution-3SUM to Exact Triangle, together with the resulting exponent transfer in Theorem 21(a). Each proposition is parameterized by an abstract deterministic time model; its concrete word-RAM interpretation is proved separately. The definitions are taken unchanged from Anthropic’s formalization and reuse the existing APSP time-model definitions.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1168-L1174; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Definitions.lean#L214-L225; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Definitions.lean#L227-L240; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Definitions.lean#L337-L349

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

namespace ThreeSumApsp

/-- `f(n) = n^{a+o(1)}`.

NOTE.  We read it as an upper bound, as the paper uses it for times and for numbers and sizes of
instances: there is a sequence `ε(n) → 0` with `|f(n)| ≤ n^{a+ε(n)}` for all large `n`. -/
def IsPowLittleO (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ᶠ n : ℕ in Filter.atTop, |f n| ≤ (n : ℝ) ^ (a + ε n)

end ThreeSumApsp


/-!
# Running-time claims of Sections 2 to 4, for an abstract notion of "solved in time T"

The paper derives many of its running times from others: "Plug Theorem 19 into Theorem 21", "This is
Corollary 26 with N = n". To check such deductions on their own, this file introduces

* the record `DetTimeModel`: for each problem of Sections 2 to 4 a predicate on running times `T`,
  read as "a deterministic algorithm solves the problem in time `T`", about which nothing is
  assumed (the record `ConditionalTimes.TimeModel` of the three conditional lemmas is another
  one, and nothing links the two);
* two closure properties of the set of running times (namespace `Closure`), which are hypotheses
  like the claims;
* the claims, each as a proposition about `M : DetTimeModel` (namespace `Claim`): time sentences of
  the paper, transfer claims ("if B is solved in time T then A is solved in time extra + calls · T")
  that the paper proves or calls straightforward, and the results it cites from the literature
  (docstrings marked CITED, names starting with an author key, such as `Claim.CH20_Theorem_5_1`).

The lemmas of the files beside this one, such as `Corollary16.of_corollary_26`, are implications
between claims, valid for every `M`. No machine is defined here and no running time is proved here.
They are applied to the interpretation `Light.lightModel`, in which `M.problem T` says that a
procedure of a program of the light language solves the problem within `T` steps; there the lemmas
carry the running times of the programs to the theorems of the paper, and the compiler carries these
to the word RAM.  For that interpretation both closure properties and every claim, at the parameters
of the paper, are proved, the cited results included: the reductions are written as programs
(theorems named `claim_…` and `closure_…`), and the derived claims follow by the lemmas.  So no
statement about the word RAM has a claim as a hypothesis.

Conventions.

* The parameters of a running time.  Sizes (`n`, `N`, `s`) are exact.  `D` is exact for the matrix
  problems (the matrices are `N × D` and `D × N`); for the two triangle problems of Section 3.1 it
  is a declared parameter, given with the input: a graph whose middle part has at most `D` vertices.
  Only `w` and `u` are upper bounds: "at most `w` query pairs (or positions)", "numbers of absolute
  value at most `u`".
* Sizes are at least 1 and bounds `u` on numbers are at least 1.  The value of a running time at
  size 0 or at a bound below 1 has no meaning: `M.problem T` says nothing about it.
* Word length.  The intended machine is the paper's word RAM (Section 2); its words are taken to
  have `Θ(log(size))` bits, and `Θ(log(n + D))` bits for the four problems that have the parameter
  `D`.  Numbers need not fit into one word, since `u` is not bounded in terms of the size: a number
  of absolute value at most `u` takes at most about `1 + log u` words, whatever the size (sizes go
  down to 1), and about `κ` words if `u = n^κ`.  This is why factors `1 + log u` appear in
  overheads.  For `u = n^{O(1)}`, the case of the paper's theorems, these factors are constants or
  logarithms.
* Calls.  As in Section 3 of the paper ("the extra time plus the total time to solve B on each
  instance created"), a transfer claim charges a call of an algorithm exactly its running time, and
  everything else to the extra time.  An algorithm that is called runs on the caller's machine,
  whose words may be longer than its own input would require. Proving the claims for an
  interpretation `M` requires that this is legitimate for `M`.
* The bound `u` on the numbers is an argument of its own, not a function of the size, because
  Theorem 21(b) fixes the bound and lets the size vary.
* `O(·)` with several parameters is written with an explicit constant.  `O(·)` in `n` alone, along
  `u = n^κ`, is `UpperBigOPow`, `UpperPowPolylog` or `UpperPowLittleO`: a running time is only ever
  bounded from above.
-/

@[expose] public section

namespace ThreeSumApsp



/-! ## The bounds in `n`, `D` and the number `w` of positions or query pairs -/







namespace Closure





end Closure

namespace Claim

/-! ## Time sentences -/





/-! ## Transfer claims that the paper proves or calls straightforward -/











/-! ## Results cited from the literature, in the form needed for Theorem 21 -/

/-- CITED.  After the proof of [CH20, Theorem 5.1]: from n integers bounded by a power of n, a
deterministic reduction computes polylogarithmically many arrays of length Õ(n), whose entries are
again bounded by a power of n, in Õ(n^{3/2}) time; three of the integers sum to 0 exactly if one of
the arrays is a yes-instance of Convolution-3SUM.  `E` is the extra time, `Num` the number of
instances, `N` their size, `mag` the bound on their numbers. -/
def CH20_Theorem_5_1 (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (E Num mag : ℕ → ℝ) (N : ℕ → ℕ) (c' κ' : ℝ),
    IsPowPolylog E (3 / 2) ∧ IsPowPolylog Num 0 ∧ IsPowPolylog (fun n => (N n : ℝ)) 1 ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ N n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') ∧
    ∀ T : ℕ → ℝ → ℝ, M.convolution3SUM T →
      ∃ T' : ℕ → ℝ → ℝ, M.threeSum T' ∧
        ∀ n : ℕ, 1 ≤ n → T' n ((n : ℝ) ^ κ) ≤ E n + Num n * T (N n) (mag n)

/-- CITED.  After the proof of [VW13, Theorem 4.3]: whether an array of `N` integers is a
yes-instance of Convolution-3SUM is decided by asking `O(√N)` times whether there is a zero
triangle, each time in an instance with `O(√N)` vertices in each part whose weights are entries of
the array, up to sign, or a filler, so that all weights are at most a constant times the bound on
the entries.

NOTE.  The time `E` of this reduction is part of the claim, because the time of Theorem 21(a) needs
`E(N) = N^{3/2+o(1)}`. -/
def VW13_Theorem_4_3 (M : DetTimeModel) : Prop :=
  ∃ (c : ℝ) (E Num : ℕ → ℝ) (size : ℕ → ℕ), 1 ≤ c ∧
    IsPowLittleO E (3 / 2) ∧ IsBigOPow Num (1 / 2) ∧ IsBigOPow (fun N => (size N : ℝ)) (1 / 2) ∧
    (∀ N : ℕ, 1 ≤ N → 1 ≤ size N) ∧
    ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
      M.convolution3SUM fun N u => E N * (1 + logU u) + Num N * T (size N) (c * u)





/-! ## Claims that are derived from the ones above -/

















/-- **Theorem 21(a)**: "3SUM on n integers of absolute value at most n^ν reduces
deterministically, in n^{3/2+o(1)} time, to n^{1/2+o(1)} instances of Exact Triangle on n^{1/2+o(1)}
vertices per part with weights of absolute value n^{O(1)} [CH20, VW13]."  `E` is the time of the
reduction, `Num` the number of instances, `size` their number of vertices per part, `mag` the bound
on their weights. -/
def Theorem_21a (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (E Num mag : ℕ → ℝ) (size : ℕ → ℕ) (c' κ' : ℝ),
    IsPowLittleO E (3 / 2) ∧ IsPowLittleO Num (1 / 2) ∧
    IsPowLittleO (fun n => (size n : ℝ)) (1 / 2) ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ size n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') ∧
    ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
      ∃ T' : ℕ → ℝ → ℝ, M.threeSum T' ∧
        ∀ n : ℕ, 1 ≤ n → T' n ((n : ℝ) ^ κ) ≤ E n + Num n * T (size n) (mag n)





/-! ## Bounds in `n` alone, along `u = n^κ` -/











end Claim

end ThreeSumApsp


