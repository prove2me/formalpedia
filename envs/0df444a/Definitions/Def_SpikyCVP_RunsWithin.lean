-- Prove2me | Definitions.Def_SpikyCVP_RunsWithin
-- name    : SpikyCVP_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:06.569825+00:00
-- url     : https://prove2.me/theorems/70e0f01a-ca7e-414f-a8da-b645deec8ad8
-- title:
--   Machine runs, time budgets and fractions of coin strings
-- statement:
--   A binary machine **runs within** $T$ steps on input $x$ with output $y$ if, started on $x$, it halts within $T$ steps with $y$ on its output stack. The budget of the main theorem is
--
--   $$T=\Big\lceil 2^{C n}\,(\ell+1)^K\,\log_2(1/\delta)\Big\rceil,$$
--
--   the form of $2^{O_p(n)}\cdot\mathrm{poly}(|I|)\cdot\log(1/\delta)$, and that of the Euclidean subroutine is $\lceil 2^{n+f(n)}(\ell+1)^K\rceil$ for a function $f(n)=o(n)$. The **coin fraction** of a property is the fraction of the $2^T$ strings of $T$ bits that have it, i.e. its probability for $T$ fair coins.
--
--   These translate the paper's running-time and probability statements into statements about one machine.
--
--   **Formalization Note** The machine is Mathlib's TM2, with the run taken per input (not $\texttt{TM2ComputableInTime}$, whose time depends on the input length alone). A TM2 halts only with every stack but the output stack empty. The paper analyzes a real-RAM and states that its results hold in the word-RAM model with polynomial overhead for every fixed rational $p$ (p.10).
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Theorem 1.1, p.3 (PDF p.5); §2.1, p.10 (PDF p.12); Theorem 2.10, p.15 (PDF p.17)

import Mathlib

namespace SpikyCVP

/-- A run of a binary-alphabet TM2 machine: on input `inp` it halts with output `out` in at most `T`
steps. Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest
Vector Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), §2.1, p.10 (PDF p.12): the results
"also hold in the word-RAM model with poly(|I|) overhead … for every fixed, rational p in 1 < p < 2".

**Formalization Note.** The paper analyzes a real-RAM; this is Mathlib's TM2 instead, run per input
(`Turing.TM2OutputsInTime`), not `TM2ComputableInTime`, whose time is a function of the input length
alone. `EvalsToInTime` counts "at most `T`" steps. `haltList` requires every stack but the output stack
to be empty at the halt. -/
def RunsWithin (M : Turing.TM2ComputableAux Bool Bool) (inp out : List Bool) (T : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (inp.map M.inputAlphabet.invFun)
    (some (out.map M.outputAlphabet.invFun)) T)

/-- The budget of Theorem 1.1, p.3: `⌈2^{C·n} · (ℓ+1)^K · log₂(1/δ)⌉`, the form of
`2^{O_p(n)} · poly(|I|) · log(1/δ)` with constants `C`, `K` and the input length `ℓ`.

**Formalization Note.** `log` is base 2 (§2.1, p.10); for `δ ≤ 1/2` the factor `log₂(1/δ)` is at least
`1`. -/
noncomputable def budget (C K n ℓ : ℕ) (δ : ℚ) : ℕ :=
  ⌈(2 : ℝ) ^ (C * n) * ((ℓ : ℝ) + 1) ^ K * Real.logb 2 (1 / (δ : ℝ))⌉₊

/-- The budget of Theorem 2.10, p.15: `⌈2^{n + f(n)} · (ℓ+1)^K⌉` for a function `f(n) = o(n)`, the form of
`2^{n+o(n)} poly(|I|)`. -/
noncomputable def budgetADS (f : ℕ → ℝ) (K n ℓ : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ ((n : ℝ) + f n) * ((ℓ : ℝ) + 1) ^ K⌉₊

/-- The fraction of coin strings of length exactly `T` that satisfy `P`, i.e. the probability of `P` for
`T` fair coins.

**Formalization Note.** The set is a subset of a finite type, so `Set.ncard` is the true count. -/
noncomputable def coinFraction (T : ℕ) (P : List Bool → Prop) : ℝ :=
  (Set.ncard {coins : List.Vector Bool T | P coins.toList} : ℝ) / (2 : ℝ) ^ T

end SpikyCVP


