-- Prove2me | Definitions.Def_SubexpPrimes_Supplement_ETH
-- name    : SubexpPrimes_Supplement_ETH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:44:24.393703+00:00
-- url     : https://prove2.me/theorems/82f97e04-dcc9-47da-91ba-88f8f22bc796
-- title:
--   Exponential Time Hypothesis (ETH) in the primitive-machine model
-- statement:
--   A machine run **halts within time** $\tau$ on an input $w$ with output $y$ if, started on $w$, the machine reaches a halted configuration after at most $\tau$ steps and its designated output tape then holds exactly $y$. No space bound is imposed.
--
--   The **Exponential Time Hypothesis** asserts that there is a real $\delta>0$ such that no deterministic machine decides satisfiability of 3-CNF formulas in time $2^{\delta n}\,\mathrm{poly}(|\varphi|)$: for every machine $M$ and every constant $K$ there are $n$ and a CNF formula $\varphi$ on $n$ variables, with at most three literals per clause, on which $M$ fails to output the bit "$\varphi$ is satisfiable" within
--
--   $$
--   K\,(|\varphi|+1)^K\,2^{\delta n}
--   $$
--
--   steps, where $|\varphi|$ is the length of the encoding of $\varphi$.
--
--   This is the hypothesis that Theorem A.19 of the paper refutes.
--
--   **Formalization Note** The machine model, the CNF type, the satisfying-assignment count and the encoding of formulas (which writes $n$ in unary before the clauses) are those of the published `SubexponentialSAT` definitions. "Satisfiable" is "the number of satisfying assignments is positive".
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), §A.7, p.72 (PDF p.74), definition of ETH

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **A run within time `τ`, with no space bound** — the time-only reading of "an algorithm that,
given …, computes … in time …" in Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), §A.7, p.72.

Started on `input`, the machine `A` reaches after some `time ≤ τ` steps a halted configuration whose
tape `out` holds exactly `output` (head on its first cell).

**Formalization Note.** The machine model is the published `SubexponentialSAT` one
(`PrimitiveMachine`, `locatedStep`, `locatedInit`), as in the base mission's `RunsWithin`; this is
`RunsWithin` without its space clause, for statements that claim no space bound. -/
def HaltsWithin (A : PrimitiveMachine) (out : Fin A.tapeCount) (input output : List Bool)
    (τ : ℝ) : Prop :=
  ∃ (time : ℕ) (final : LocatedCfg A),
    Trace (locatedStep A) time (locatedInit A input) final ∧
    (∃ b : Bool, final.config.state = Sum.inl b) ∧
    final.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
    (time : ℝ) ≤ τ

/-- **The Exponential Time Hypothesis** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), §A.7, p.72: "there is a δ > 0 such that no
algorithm decides satisfiability of 3-CNF formulas on n variables in time 2^{δn} poly(|φ|)".

There is a real `δ > 0` such that no machine `M` (with any output tape) and no constant `K` satisfy:
for every `n` and every CNF formula `φ` on the variables `Fin n` whose clauses have at most three
literals, `M` started on the encoding of `φ` halts with the one-bit answer "`φ` is satisfiable" within
`K (|φ| + 1)^K 2^{δ n}` steps.

**Formalization Note.** "Algorithm" is a `PrimitiveMachine` of the published `SubexponentialSAT`
model; `|φ|` is the length of `Encoding.encodeCNF φ` (which writes `n` in unary first); `poly(|φ|)` is
`K (|φ| + 1)^K`; satisfiable means `0 < SAT.count φ`; a 3-CNF is a CNF of width at most 3. -/
def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (M : PrimitiveMachine) (out : Fin M.tapeCount),
    ¬ ∃ K : ℕ, ∀ (n : ℕ) (φ : SAT.CNF (Fin n)), SAT.WidthAtMost 3 φ →
      HaltsWithin M out (Encoding.encodeCNF φ) [decide (0 < SAT.count φ)]
        ((K : ℝ) * (((Encoding.encodeCNF φ).length : ℝ) + 1) ^ K * (2 : ℝ) ^ (δ * (n : ℝ)))

end SubexpPrimes.Supplement


