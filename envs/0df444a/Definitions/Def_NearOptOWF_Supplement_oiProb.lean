-- Prove2me | Definitions.Def_NearOptOWF_Supplement_oiProb
-- name    : NearOptOWF_Supplement_oiProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:11:18.606359+00:00
-- url     : https://prove2.me/theorems/a282e43c-5bce-4a2f-81f4-c69078545ccd
-- title:
--   Output-intractability success probability
-- statement:
--   For a sampleable family $\mathcal H$ of functions $\{0,1\}^n\to\{0,1\}^{m(n)}$, an arity $t$, a $t$-ary relation ensemble $\mathcal R$ and an adversary $A$, the success probability at input length $n$ is
--   $$
--   \Pr_{f\leftarrow\mathcal H,\ A\text{'s coins}}\Bigl[x_i\ne x_j\ \text{for all}\ i\ne j\ \text{and}\ (f(x_1),\dots,f(x_t))\in\mathcal R_n\ :\ A(1^n, f)\to(x_1,\dots,x_t)\Bigr],
--   $$
--   where the output of $A$ must have length exactly $t(n)\cdot n$ and is split into $t$ blocks $x_1,\dots,x_t\in\{0,1\}^n$. $\mathcal H$ is $\epsilon$-secure $\mathcal R$-output intractable when every PPT $A$ has success probability at most $\epsilon(n)$ for all sufficiently large $n$.
--
--   **Formalization Note** $A$ receives $1^n$ and the description of $f$, as in the base inversion probability; the paper's security parameter $\lambda=\mathrm{poly}(n,m,t)$ is a parameter of the construction.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 5.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_NearOptOWF_FunFamily
import Definitions.Def_NearOptOWF_Inverter
import Definitions.Def_NearOptOWF_Supplement_blocks
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NearOptOWF.Supplement

open LaconicBarrier

open Classical in
/-- The **output-intractability success probability** of the adversary `A` against the family `H` for the
`t`-ary relation ensemble `R`, at input length `n` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 5.1, p.23 (PDF p.25):
"`Pr[x_i ≠ x_j for all i ≠ j and (H_k(x₁), …, H_k(x_t)) ∈ R_m : A(1^λ, H_k) → (x₁, …, x_t)]`"):
sample `f ← H` and `A`'s coins, run `A` on `(1ⁿ, f)`, read its output as `t(n)` blocks `x₁, …, x_t` of
`n` bits, and succeed when the output has length exactly `t(n)·n`, the `x_i` are pairwise distinct, and
`(f(x₁), …, f(x_t)) ∈ R n`.

**Formalization Note** `A` receives `1ⁿ` and the description of `f`, as in the base `invProb`; the paper's
`1^λ` is `λ = poly(n, m, t)`, a parameter of the construction that `A` can compute from `n`. The value
`f(x_i)` is read as an element of `{0,1}^{m(n)}` through its first `m(n)` bits (exactly its bits, since an
efficient family's circuits have `m(n)` outputs). -/
noncomputable def oiProb {m : ℕ → ℕ} (H : FunFamily m) (t : ℕ → ℕ)
    (R : (n : ℕ) → Set (Fin (t n) → Fin (m n) → Bool)) (A : Inverter) (n : ℕ) : ℝ :=
  coinAvg (H.coins n) fun ρ =>
    coinAvg (A.coins (KarpLiptonOM.tupleEnc [unary n, (H.samp n ρ).code]).length) fun r =>
      if (A.run [unary n, (H.samp n ρ).code] (bits r)).length = t n * n ∧
          (∀ i j : Fin (t n), i ≠ j →
            blocks n (t n) (A.run [unary n, (H.samp n ρ).code] (bits r)) i ≠
              blocks n (t n) (A.run [unary n, (H.samp n ρ).code] (bits r)) j) ∧
          (fun (i : Fin (t n)) (j : Fin (m n)) =>
            ((H.samp n ρ).eval (blocks n (t n) (A.run [unary n, (H.samp n ρ).code] (bits r)) i)).getD
              j.1 false) ∈ R n
      then 1 else 0

end NearOptOWF.Supplement


