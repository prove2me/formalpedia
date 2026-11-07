-- Prove2me | Definitions.Def_QiOPoQ_UPPT
-- name    : QiOPoQ_UPPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:00.144257+00:00
-- url     : https://prove2.me/theorems/1bc7a882-520a-45cc-9d2c-11217375d09b
-- title:
--   Uniform classical probabilistic polynomial-time algorithms
-- statement:
--   A classical PPT algorithm is a deterministic polynomial-time map together with a polynomial $q$: on input $x$ it reads $q(|x|)$ uniform coins $r$ and outputs the map's value on $(x,r)$. Every probability in the paper is an average over such finitely many coins and finitely many measurement outcomes.
--
--   The obfuscator is an algorithm of this kind: it is classical (footnote 11 of the paper) and uniform.
--
--   **Formalization Note** A machine that uses at most $q(|x|)$ coins is one that reads exactly $q(|x|)$ of them, so a fixed polynomial coin count loses nothing. Polynomial time is the published Turing-machine notion on binary strings.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3, p.13; Definition 3.1 and footnote 11, p.14

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

/-- The average of `g` over `m` uniform coins `r ∈ {0,1}^m`: `E_r[g(r)] = 2^{−m} Σ_r g(r)`.
Every probability in the paper (Definitions 3.1–3.3, 4.2; Lemmas 4.4, 4.5; Theorem 4.7) is over
finitely many uniform coins and finitely many measurement outcomes. -/
noncomputable def avgCoins (m : ℕ) (g : Str → ℝ) : ℝ :=
  (∑ r : Fin m → Bool, g (List.ofFn r)) / 2 ^ m

/-- **A (uniform) classical PPT algorithm.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable
Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256
fe2f9210…), §3, p.13 ("probabilistic polynomial-time"), Definition 3.1, p.14 (the obfuscator
"is a PPT algorithm", footnote 11: classical). A deterministic polynomial-time map `run` and a
polynomial `coins`: on input `x` the algorithm reads `coins(|x|)` uniform coins `r` and outputs
`run (pair x r)`.

**Formalization Note.** Polynomial time is the published `QAlgorithms.Complexity.PolyTimeComputable`
(Mathlib `TM2ComputableInPolyTime`, binary strings). A machine that uses at most `p(|x|)` coins
is one that reads exactly `p(|x|)` coins, so a fixed polynomial coin count loses nothing. -/
structure UPPT where
  run : Str → Str
  run_poly : PolyTimeComputable run
  coins : Polynomial ℕ

/-- `E[g(M(x))]` over the coins of `M`. -/
noncomputable def UPPT.expect (M : UPPT) (x : Str) (g : Str → ℝ) : ℝ :=
  avgCoins (M.coins.eval x.length) fun r => g (M.run (pair x r))

/-- `M(x; r)`: `M` run with the explicit coin string `r` (its first `coins(|x|)` bits; the rest
is ignored). Used for `qiO(1^λ, C_{b_i,λ}; r_i)` in Figure 6. -/
def UPPT.runWith (M : UPPT) (x r : Str) : Str :=
  M.run (pair x (r.take (M.coins.eval x.length)))

end QiOPoQ


