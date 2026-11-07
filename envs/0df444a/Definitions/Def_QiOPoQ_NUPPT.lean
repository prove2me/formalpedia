-- Prove2me | Definitions.Def_QiOPoQ_NUPPT
-- name    : QiOPoQ_NUPPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:26.548207+00:00
-- url     : https://prove2.me/theorems/1616074b-6d91-4d9a-82e5-fc69fb881e09
-- title:
--   Non-uniform classical probabilistic polynomial-time algorithms
-- statement:
--   A non-uniform classical PPT algorithm consists of a deterministic polynomial-time map, an advice string $a_\lambda$ of length at most $p(\lambda)$ for a polynomial $p$, and a polynomial coin count. On $(1^\lambda,x)$ it reads uniform coins $r$, polynomially many in $\lambda+|x|$, and outputs the map's value on $(a_\lambda,1^\lambda,x,r)$. A decision is the output string $1$ ("accept") or $0$. These are the adversaries of Definition 3.2, the classical provers of Definition 3.3, the inverters of one-way functions, and the machine of Definition 4.2.
--
--   The polynomial bound on the advice is essential: with unbounded advice every language would lie in i.o.P/poly, and the assumption of the main theorem would be false.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3, p.13 ("we consider non-uniform adversaries throughout this paper"); Definition 4.2, p.18

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

/-- **A non-uniform classical PPT algorithm.** §3, p.13: "In general, we consider non-uniform
adversaries throughout this paper." A polynomial-time map `run`, an advice string `advice λ` of
length at most `adviceLen(λ)` for each security parameter `λ`, and a polynomial `coins`: on
`(1^λ, x)` the algorithm reads `coins(λ + |x|)` uniform coins `r` and outputs
`run (pair (advice λ) (pair (unary λ) (pair x r)))`.

**Formalization Note.** The polynomial bound on the advice is essential: with unbounded advice
every language would be in i.o.P/poly. A bit is output as `[true]` ("= 1") or `[false]`. Used
for the qiO adversaries (Definition 3.2), the algorithm `M` of Definition 4.2, one-way function
inverters and classical provers (Definition 3.3). -/
structure NUPPT where
  run : Str → Str
  run_poly : PolyTimeComputable run
  advice : ℕ → Str
  adviceLen : Polynomial ℕ
  advice_le : ∀ n, (advice n).length ≤ adviceLen.eval n
  coins : Polynomial ℕ

/-- `E[g(A(1^λ, x))]` over the coins of `A`. -/
noncomputable def NUPPT.expect (A : NUPPT) (n : ℕ) (x : Str) (g : Str → ℝ) : ℝ :=
  avgCoins (A.coins.eval (n + x.length)) fun r =>
    g (A.run (pair (A.advice n) (pair (unary n) (pair x r))))

/-- `Pr[A(1^λ, x) = 1]`. -/
noncomputable def NUPPT.acc (A : NUPPT) (n : ℕ) (x : Str) : ℝ :=
  A.expect n x fun o => if o = [true] then 1 else 0

end QiOPoQ


