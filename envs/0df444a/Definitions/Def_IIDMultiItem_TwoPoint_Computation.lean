-- Prove2me | Definitions.Def_IIDMultiItem_TwoPoint_Computation
-- name    : IIDMultiItem_TwoPoint_Computation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:58:43.879374+00:00
-- url     : https://prove2.me/theorems/2caf807c-31a4-4588-86cd-c2b36580c86d
-- title:
--   Inputs, sizes and outputs of the two computational problems of Theorem 3.3 (outcome at a profile; the value (3.6))
-- statement:
--   The computational clause of Theorem 3.3 concerns rational $a,b,p$. Following §1.1 ("we specify the prior F by its rational support points and associated probabilities, and provide the parameters n and m in unary") and §2.3 (polynomial time means time polynomial in $n+m+$ the bit length of the input), an instance of the **value problem** is $n$ and $m$ in unary followed by $a$, $b$, $p$ written as fractions (binary numerator and positive binary denominator, not necessarily reduced); it is well formed when $n,m\ge1$, $0<a<b$ and $0<p<1$. The required output is the value (3.6) in lowest terms. An instance of the **outcome problem** adds a profile $S$ written as $n$ rows of $m$ bits (bit $j$ of row $i$ is $1$ iff $j\in S_i$); the required output lists, for $i=1,\dots,n$, the $m$ bits of $A_i$ followed by the payment $s_i$ in lowest terms, for the auction with the reserves (3.2). A rational number in lowest terms is written as a sign bit, then $|\text{numerator}|$ and the denominator in the self-delimiting binary code. The size of an instance is the length of its code.
--
--   **Formalization Note.** Uses the published `HypergraphUnreliability.FPRAS` machine model (`Frac`, `natCode`, `fracCode`, `PolyComputesIn`). `unaryCode k` is $k$ ones then a zero; `ratCode r` is the sign bit, `natCode |r.num|`, `natCode r.den` (a Lean rational is always reduced with positive denominator); `realRatCode x` is `ratCode` of the unique rational equal to the real `x` (empty for an irrational `x`). `ValueInput`, `OutcomeInput` are the instances, `Valid` the well-formedness predicates, `encode` the input codes and `answer` the required outputs; `OutcomeInput.profile` reads the profile from its rows.
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 2 (PDF 4), §1.1; p. 12 (PDF 14), §2.3; p. 14 (PDF 16), Theorem 3.3; pp. 38–39 (PDF 40–41), §B.4

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IIDMultiItem_TwoPoint_Counts
import Definitions.Def_IIDMultiItem_TwoPoint_Auction

open scoped BigOperators

/-!
# Inputs and outputs of the two computational problems of Theorem 3.3

Liu, Liu, Wang, *Optimal Multi-Item Auctions with I.I.D. Values*, arXiv:2610.11051 (held version,
PDF of 2026-11-03, sha256 983080a4…), §1.1, p. 2 ("we specify the prior F by its rational support
points and associated probabilities, and provide the parameters n and m in unary"); §2.3, p. 12
(polynomial time = polynomial in `n + m + bit(F)`); Theorem 3.3, p. 14.

The machine model is the published `HypergraphUnreliability.FPRAS` one: written fractions `Frac`
(binary numerator, binary denominator, not necessarily reduced), self-delimiting `natCode`,
`fracCode`, and `PolyComputesIn`. Here `n` and `m` are written in unary, `a`, `b`, `p` as written
fractions, and a profile as `n` rows of `m` bits (bit `j` of row `i` is `1` iff `j ∈ S_i`). The
size of an input is the length of its code. A rational output is written in lowest terms (`ℚ`
is always reduced): a sign bit (`true` iff negative), then `|numerator|` and the denominator in
`natCode`.
-/

namespace IIDMultiItem.TwoPoint

open HypergraphUnreliability.FPRAS

/-- `k` in unary: `k` ones, then a zero. -/
def unaryCode (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- A rational in lowest terms: sign bit (`true` iff negative), `|num|`, `den`. -/
def ratCode (r : ℚ) : List Bool := [decide (r < 0)] ++ natCode r.num.natAbs ++ natCode r.den

/-- The code of a real number that is rational (`ratCode` of the unique rational equal to it);
the empty list for an irrational number. -/
noncomputable def realRatCode (x : ℝ) : List Bool :=
  open Classical in
  if h : ∃ r : ℚ, (r : ℝ) = x then ratCode (Classical.choose h) else []

/-- An instance of the value problem: `n`, `m` and the written rationals `a`, `b`, `p` of
`F = p δ_a + (1 − p) δ_b`. -/
structure ValueInput where
  n : ℕ
  m : ℕ
  a : Frac
  b : Frac
  p : Frac

/-- A well-formed instance: `n, m ≥ 1`, positive denominators, `0 < a < b` and `0 < p < 1`. -/
def ValueInput.Valid (x : ValueInput) : Prop :=
  1 ≤ x.n ∧ 1 ≤ x.m ∧ 0 < x.a.den ∧ 0 < x.b.den ∧ 0 < x.p.den ∧
    0 < x.a.val ∧ x.a.val < x.b.val ∧ 0 < x.p.val ∧ x.p.val < 1

/-- The input code: `n` and `m` in unary, then `a`, `b`, `p`. -/
def ValueInput.encode (x : ValueInput) : List Bool :=
  unaryCode x.n ++ unaryCode x.m ++ fracCode x.a ++ fracCode x.b ++ fracCode x.p

/-- The required output: the lowest-terms code of the value (3.6). -/
noncomputable def ValueInput.answer (x : ValueInput) : List Bool :=
  realRatCode (revFormula (x.a.val : ℝ) (x.b.val : ℝ) (x.p.val : ℝ) x.n x.m)

/-- An instance of the outcome problem: a value instance and a profile, as a list of rows. -/
structure OutcomeInput extends ValueInput where
  prof : List (List Bool)

/-- A well-formed outcome instance: a well-formed value instance and `n` rows of `m` bits. -/
def OutcomeInput.Valid (x : OutcomeInput) : Prop :=
  x.toValueInput.Valid ∧ x.prof.length = x.n ∧ ∀ row ∈ x.prof, row.length = x.m

/-- The input code: the value instance, then the profile row by row. -/
def OutcomeInput.encode (x : OutcomeInput) : List Bool :=
  x.toValueInput.encode ++ x.prof.flatten

/-- The profile `S` written in `x`: `S_i = {j : bit j of row i is 1}`. -/
def OutcomeInput.profile (x : OutcomeInput) : Fin x.n → Finset (Fin x.m) :=
  fun i => Finset.univ.filter (fun j => (x.prof.getD i.val []).getD j.val false = true)

/-- The required output: for each buyer `i = 1, …, n` in turn, the `m` bits of `A_i` (bit `j`
is `1` iff `j ∈ A_i`), then the lowest-terms code of `s_i`, for the auction with the reserves
(3.2) at the written profile. -/
noncomputable def OutcomeInput.answer (x : OutcomeInput) : List Bool :=
  open Classical in
  (List.finRange x.n).flatMap (fun i =>
    (List.finRange x.m).map (fun j =>
        decide (j ∈ alloc (reserveStar (x.a.val : ℝ) (x.b.val : ℝ) (x.p.val : ℝ)) x.profile i)) ++
      realRatCode (payment (x.a.val : ℝ) (x.b.val : ℝ)
        (reserveStar (x.a.val : ℝ) (x.b.val : ℝ) (x.p.val : ℝ)) x.profile i))

end IIDMultiItem.TwoPoint


