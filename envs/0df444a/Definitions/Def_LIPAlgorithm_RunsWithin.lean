-- Prove2me | Definitions.Def_LIPAlgorithm_RunsWithin
-- name    : LIPAlgorithm_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:36.459821+00:00
-- url     : https://prove2.me/theorems/81529a6c-3d6b-4fde-a888-f701a96434c1
-- title:
--   Machine runs, time budgets and fractions of coin strings
-- statement:
--   A binary machine **runs within** $T$ steps on input $x$ with output $y$ if, started on $x$, it halts within $T$ steps with $y$ on its output stack. The budget of the main theorem is
--
--   $$\Big\lceil \big(C\,n\sqrt{\log(n+2)}\big)^n(\ell+1)^K\Big\rceil,$$
--
--   and that of Theorem 7.1 is $\lceil (Cn\sqrt{\log(n+2)})^n\,2^{(\log_2(\kappa+2))^K}(\kappa+\ell+1)^K\rceil$. The **coin fraction** of a property is the fraction of the $2^T$ strings of $T$ bits that have it, which is the probability of the property for $T$ fair coins.
--
--   These translate the convention $O(f(n))^n=(Cf(n))^n$ with a universal constant $C$ and the suppressed multiplicative $\mathrm{poly}(n,\mathrm{bits})$.
--
--   **Formalization Note** The machine is Mathlib's TM2, with the run taken per input. A TM2 halts only with every stack but the output stack empty and its variable back at its initial value. $\log(n+2)$ replaces $\log n$, which vanishes at $n=1$; for $n\ge2$ the class of bounds is unchanged.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), footnote 2, p.2; Remark 2.2, p.10

import Mathlib

namespace LIPAlgorithm

/-- A run of a binary-alphabet TM2 machine: on input `inp` it halts with output `out` in at most `T`
steps. The paper names no machine model (`Remark 2.2`, p.10 suppresses "a multiplicative poly(n, bits)
factor").

**Formalization Note.** This is `Turing.TM2OutputsInTime` per input, not `TM2ComputableInTime`, whose time
is a function of the input length alone. `EvalsToInTime` counts "at most `T`" steps. `haltList` requires
every stack but the output stack to be empty at the halt, and the variable to be back at its initial value. -/
def RunsWithin (M : Turing.TM2ComputableAux Bool Bool) (inp out : List Bool) (T : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (inp.map M.inputAlphabet.invFun)
    (some (out.map M.outputAlphabet.invFun)) T)

/-- The budget of the main theorem, `⌈(C·n·√log(n+2))ⁿ·(ℓ+1)^K⌉`: footnote 2, p.2 ("O(f(n))n stands for
(Cf(n))n, where C > 0 is a universal constant") and Remark 2.2, p.10 (a multiplicative polynomial in the
encoding length `ℓ` is suppressed).

**Formalization Note.** `log(n+2)` replaces `log n`, which is `0` at `n = 1`. For `n ≥ 2`,
`log(n+2) ≤ 2·log n`, so the class of bounds is the same up to the constant `C`. -/
noncomputable def budget (C K n ℓ : ℕ) : ℕ :=
  ⌈((C : ℝ) * n * Real.sqrt (Real.log ((n : ℝ) + 2))) ^ n * ((ℓ : ℝ) + 1) ^ K⌉₊

/-- The budget of Theorem 7.1, p.38: `O(n√log n)ⁿ·2^{polylog(κ)}·poly(κ)`, up to a polynomial in the
encoding length `ℓ` (Remark 2.2, p.10):
`⌈(C·n·√log(n+2))ⁿ · 2^{(log₂(κ+2))^K} · (κ+ℓ+1)^K⌉`.

**Formalization Note.** `κ + 2` keeps the logarithm positive at `κ = 0`, `1`; the exponent `K` is shared
by the polylogarithm and both polynomials, which loses nothing since the constants are existential. -/
noncomputable def budgetWR (C K n κ ℓ : ℕ) : ℕ :=
  ⌈((C : ℝ) * n * Real.sqrt (Real.log ((n : ℝ) + 2))) ^ n *
      (2 : ℝ) ^ (Real.logb 2 ((κ : ℝ) + 2) ^ K) * ((κ : ℝ) + (ℓ : ℝ) + 1) ^ K⌉₊

/-- The fraction of coin strings of length exactly `T` that satisfy `P`, i.e. the probability of `P` for
`T` fair coins.

**Formalization Note.** The set is a subset of a finite type, so `Set.ncard` is the true count. -/
noncomputable def coinFraction (T : ℕ) (P : List Bool → Prop) : ℝ :=
  (Set.ncard {coins : List.Vector Bool T | P coins.toList} : ℝ) / (2 : ℝ) ^ T

end LIPAlgorithm


