-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_CVerifier
-- name    : QAdvFew_PoQOracle_CVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:44.160665+00:00
-- url     : https://prove2.me/theorems/7541bd14-b65a-43ea-8d60-7228d5e2bf18
-- title:
--   Classical PPT oracle verifier
-- statement:
--   A **classical PPT oracle verifier** draws coins $r\in\{0,1\}^{\mathrm{coins}(n)}$. In round $j<R(n)$ it sends the $\ell(n)$-bit message computed by an oracle machine on the common input, $r$ and the messages so far, and after the last round it outputs the first bit computed on the whole transcript. $R$, $\ell$ and the coin count are polynomials.
--
--   Its likelihood $w_V(\tau,b)$ is the fraction of coin strings with which it produces its messages of $\tau$ and outputs $b$.
--
--   **Formalization Note** The machine is run for a polynomial clock and its output read off the work tape. A clocked machine runs in polynomial time, and every polynomial-time machine is its own clocked version.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.8, p. 13 (PDF p. 15); Definition 3.26, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_Protocol

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **classical PPT oracle verifier** in a polynomial-round protocol with classical communication
(Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Definition 3.8, p. 13 (PDF p. 15), and Definition 3.26, p. 19 (PDF p. 21)). On common input `s` of
length parameter `n`, it draws coins `r ∈ {0,1}^{coins(n)}`; in round `j < R(n)` it sends the
`ℓ(n)`-bit message computed by the oracle machine `M` on `(s, r, v₀, p₀, …, v_{j−1}, p_{j−1})`, and
after the last round it outputs the first bit computed by `M` on `(s, r, whole transcript)`.

**Formalization Note** `M` is run for `clock(|input|)` steps and its output read off the work tape;
a clocked machine is the same as a polynomial-time machine (every polynomial-time machine is its own
clocked version, and a clocked machine runs in polynomial time). The number of rounds `R`, the
message length `ℓ` and the coin count are polynomials in `n`. -/
structure CVerifier where
  M : OTM
  clock : Polynomial ℕ
  coins : Polynomial ℕ
  R : Polynomial ℕ
  ℓ : Polynomial ℕ

namespace CVerifier

/-- The output of the verifier's machine on `(s, r, ms)`. -/
def run (V : CVerifier) (O : Oracle) (s r : Str) (ms : List Str) : Str :=
  V.M.output O (tup (s :: r :: ms)) (V.clock.eval (tup (s :: r :: ms)).length)

/-- The verifier's message in round `j`. -/
def msg (V : CVerifier) (O : Oracle) (s : Str) (n : ℕ) (r : Str)
    (τ : Transcript (V.R.eval n) (V.ℓ.eval n)) (j : ℕ) : Msg (V.ℓ.eval n) :=
  padTo _ (V.run O s r (τ.prefixV j))

/-- The verifier's decision on the whole transcript. -/
def dec (V : CVerifier) (O : Oracle) (s : Str) (n : ℕ) (r : Str)
    (τ : Transcript (V.R.eval n) (V.ℓ.eval n)) : Bool :=
  (V.run O s r τ.all).headD false

/-- The verifier's likelihood `w_V(τ, b)`: the fraction of coin strings `r` with which the verifier,
receiving the prover messages of `τ`, sends its own messages of `τ` and outputs `b`. -/
noncomputable def lik (V : CVerifier) (O : Oracle) (s : Str) (n : ℕ)
    (τ : Transcript (V.R.eval n) (V.ℓ.eval n)) (b : Bool) : ℝ :=
  ((Finset.univ.filter (fun r : Fin (V.coins.eval n) → Bool =>
      (∀ j : Fin (V.R.eval n), V.msg O s n (List.ofFn r) τ j = (τ j).1) ∧
        V.dec O s n (List.ofFn r) τ = b)).card : ℝ) / (2 ^ V.coins.eval n : ℝ)

end CVerifier

end QAdvFew.PoQOracle


