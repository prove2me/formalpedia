-- Prove2me | Definitions.Def_UniqueOptScores_IsClocked
-- name    : UniqueOptScores_IsClocked
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:53.863171+00:00
-- url     : https://prove2.me/theorems/05e1c1aa-dfb6-4598-b7ea-f45ae8388658
-- title:
--   Polynomial clocks valid for every oracle
-- statement:
--   Let $M$ be a deterministic oracle Turing machine. $M$ **halts with output $y$ within $t$ steps** on input $w$ with oracle $A$ if its run reaches the halting configuration with $y$ on the output tape after at most $t$ steps (an oracle call counts as one step).
--
--   A polynomial $t$ is a **clock** for $M$ if for **every** oracle $A$ and every input $w$ the machine halts with some output within $t(|w|)$ steps. The paper requires this of every machine in every class: "the polynomial running-time bound must hold for every oracle and every computation path", and "all machines carry polynomial clocks valid on all candidates and all oracle answers". Uniformity over oracles is what lets an oracle construction enumerate competitors once and for all.
--
--   **Formalization Note** The halting configuration is Mathlib's `Turing.haltList` (empty auxiliary stacks, output on the output stack), as in `Turing.TM2OutputsInTime`. The clock is a polynomial with natural coefficients evaluated at the input length.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2 (Relativization), p.15; Section 4, p.16 ("All machines carry polynomial clocks valid on all candidates and all oracle answers")

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_setOracle

namespace UniqueOptScores

/-- **An oracle machine halts within `t` steps with output `out`.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.15 and §4, p.16.

`HaltsWithin OM A w out t` holds when the run of `OM` with oracle `A` on input `w` reaches the
halting configuration with output `out` after at most `t` steps.

**Formalization Note.** The halting configuration is Mathlib's `Turing.haltList` (the TM2 output
convention, as in `Turing.TM2OutputsInTime`); every step, including an oracle call, costs one. -/
def HaltsWithin (OM : HMBinPacking.OracleMachine) (A : Set (List Bool)) (w out : List Bool)
    (t : ℕ) : Prop :=
  ∃ s ≤ t, HMBinPacking.oRun OM (setOracle A) w s =
    some (Turing.haltList OM.M.tm (out.map OM.M.outputAlphabet.symm))

/-- **A polynomial clock valid for every oracle.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.15: "For each polynomial-time oracle machine, the polynomial running-time bound
must hold for every oracle and every computation path"; §4, p.16: "All machines carry polynomial
clocks valid on all candidates and all oracle answers."

`IsClocked OM t` holds when, for **every** oracle `A` and every input `w`, the machine halts with
some output within `t(|w|)` steps.

**Formalization Note.** The clock is a polynomial `t` with natural coefficients and is uniform over
all oracles `A : Set (List Bool)`, as the paper requires. -/
def IsClocked (OM : HMBinPacking.OracleMachine) (t : Polynomial ℕ) : Prop :=
  ∀ (A : Set (List Bool)) (w : List Bool), ∃ out, HaltsWithin OM A w out (t.eval w.length)

end UniqueOptScores


