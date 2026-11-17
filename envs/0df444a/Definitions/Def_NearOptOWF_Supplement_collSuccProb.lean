-- Prove2me | Definitions.Def_NearOptOWF_Supplement_collSuccProb
-- name    : NearOptOWF_Supplement_collSuccProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:07:21.797898+00:00
-- url     : https://prove2.me/theorems/920e857c-111e-4205-b333-f18dbcc06a4f
-- title:
--   Collision probability $\Pr[A(f)\ \text{outputs a collision on}\ y]$
-- statement:
--   For a randomized algorithm $A$, a circuit $f$ with $n$ inputs and a string $y$, $A$ is run on $(1^n, f)$ and its output is read as two $n$-bit halves $(x, x')$. It **outputs a collision on $y$** when the output has length $2n$, $x\ne x'$, and $f(x) = f(x') = y$. This definition is the probability of that event over $A$'s coins:
--   $$
--   \Pr\bigl[A(f)\ \text{outputs a collision on}\ y\bigr].
--   $$
--   It is the success probability in the second hypothesis of Theorem 5.3.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §5.1 and Theorem 5.3, second bullet, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_NearOptOWF_Inverter
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- `Pr[A(f) outputs a collision on y]` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §5.1 and Theorem 5.3, second bullet, p.24 (PDF p.26)):
over `A`'s coins, `A` is run on `(1ⁿ, f)`; its output, read as two `n`-bit halves `(x, x′)`, is a
collision on `y` when it has length `2n`, `x ≠ x′` and `f(x) = f(x′) = y`.

**Formalization Note** The pair is the fixed split of a `2n`-bit output into its first and last `n`
bits; any other output is `⊥`. -/
noncomputable def collSuccProb (A : Inverter) {n : ℕ} (f : MCircuit n) (y : List Bool) : ℝ :=
  coinAvg (A.coins (KarpLiptonOM.tupleEnc [unary n, f.code]).length) fun r =>
    if (A.run [unary n, f.code] (bits r)).length = 2 * n ∧
        (A.run [unary n, f.code] (bits r)).take n ≠ (A.run [unary n, f.code] (bits r)).drop n ∧
        f.eval ((A.run [unary n, f.code] (bits r)).take n) = y ∧
        f.eval ((A.run [unary n, f.code] (bits r)).drop n) = y then 1 else 0

end NearOptOWF.Supplement


