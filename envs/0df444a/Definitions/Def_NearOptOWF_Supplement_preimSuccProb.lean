-- Prove2me | Definitions.Def_NearOptOWF_Supplement_preimSuccProb
-- name    : NearOptOWF_Supplement_preimSuccProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:05:57.742202+00:00
-- url     : https://prove2.me/theorems/a91fa548-f2e5-4140-bfa4-4b9ca80e2a19
-- title:
--   Inversion probability $\Pr[A(f,y)\in f^{-1}(y)]$ for fixed $f, y$
-- statement:
--   For a randomized algorithm $A$, a circuit $f$ with $n$ inputs and a string $y$, this is the probability, over $A$'s coins only, that $A$ run on $(1^n, f, y)$ outputs a string $x\in\{0,1\}^n$ with $f(x) = y$:
--   $$
--   \Pr\bigl[A(f, y)\ \text{outputs a string in}\ f^{-1}(y)\bigr].
--   $$
--   It is the success probability in the second hypothesis of Theorem 4.3.
--
--   **Formalization Note** $f$ is given to $A$ by its circuit description, as in the base inversion probability.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.3, second bullet, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_NearOptOWF_Inverter
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- `Pr[A(f, y) outputs a string in f⁻¹(y)]` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.3, second bullet, p.13 (PDF p.15)): over
`A`'s coins only, `A` is run on `(1ⁿ, f, y)` and succeeds when its output `x` has length `n` and
`f(x) = y`.

**Formalization Note** `f` is given by its description `MCircuit.code`, as in the base `invProb`. -/
noncomputable def preimSuccProb (A : Inverter) {n : ℕ} (f : MCircuit n) (y : List Bool) : ℝ :=
  coinAvg (A.coins (KarpLiptonOM.tupleEnc [unary n, f.code, y]).length) fun r =>
    if (A.run [unary n, f.code, y] (bits r)).length = n ∧
        f.eval (A.run [unary n, f.code, y] (bits r)) = y then 1 else 0

end NearOptOWF.Supplement


