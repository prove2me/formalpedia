-- Prove2me | Definitions.Def_NearOptOWF_invProb
-- name    : NearOptOWF_invProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:39.014211+00:00
-- url     : https://prove2.me/theorems/2918b676-0396-4fb6-ab7d-4c9e516efc17
-- title:
--   Inversion probability $\Pr_{f, x}[A(f, f(x)) \in f^{-1}(f(x))]$
-- statement:
--   For a family $\mathcal H$ and an algorithm $A$, the **inversion probability** at input length $n$ is
--   $$
--   \Pr_{f \leftarrow \mathcal H,\ x \leftarrow \{0,1\}^n,\ A}\bigl[A(1^n, f, f(x)) = x' \ \wedge\ x' \in \{0,1\}^n \ \wedge\ f(x') = f(x)\bigr].
--   $$
--   The function $f$ is given to $A$ by its circuit description. Success means finding any pre-image of $f(x)$, not necessarily $x$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13); Lemma 4.10, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_NearOptOWF_FunFamily
import Definitions.Def_NearOptOWF_Inverter
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NearOptOWF

open LaconicBarrier

/-- The **inversion probability** of `A` against the family `H` at input length `n` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem
4.1, p.11 (PDF p.13); Lemma 4.10, p.17 (PDF p.19): "`Pr_{f←H, x←{0,1}ⁿ}[A(f, f(x)) = x′ ∧ f(x′) =
f(x)]`"): sample `f ← H`, `x ← {0,1}ⁿ` and `A`'s coins, run `A` on `(1ⁿ, f, f(x))`, and succeed when its
output `x′` lies in `{0,1}ⁿ` and `f(x′) = f(x)`.

**Formalization Note** `f` is given to `A` by its description `MCircuit.code`. Success asks for any
pre-image of `f(x)`, not for `x`. -/
noncomputable def invProb {m : ℕ → ℕ} (H : FunFamily m) (A : Inverter) (n : ℕ) : ℝ :=
  coinAvg (H.coins n) fun ρ => coinAvg n fun x =>
    coinAvg (A.coins (KarpLiptonOM.tupleEnc
        [unary n, (H.samp n ρ).code, (H.samp n ρ).eval (bits x)]).length) fun r =>
      if (A.run [unary n, (H.samp n ρ).code, (H.samp n ρ).eval (bits x)] (bits r)).length = n ∧
          (H.samp n ρ).eval (A.run [unary n, (H.samp n ρ).code, (H.samp n ρ).eval (bits x)]
            (bits r)) = (H.samp n ρ).eval (bits x)
      then 1 else 0

end NearOptOWF


