-- Prove2me | Definitions.Def_HypercliqueFalse_matMul
-- name    : HypercliqueFalse_matMul
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:57.174927+00:00
-- url     : https://prove2.me/theorems/e284ae11-edae-4c88-b7a2-2385e34603da
-- title:
--   Rectangular integer matrix multiplication (word RAM problem)
-- statement:
--   The problem of **multiplying an $n \times d$ by a $d \times m$ integer matrix** on the published word RAM. An instance at scale $s$ consists of dimensions with $d \le n \le s$ and $d \le m \le s$, a matrix $X \in \mathbb Z^{n\times d}$ and a matrix $Y \in \mathbb Z^{d \times m}$. The input is $n, m, d$ followed by $X$ and $Y$ row by row; the machine must write the $nm$ entries of $XY$ row by row after the input.
--
--   Its running time is the paper's $\mathrm{MM}(n, d, m)$, bounded with Strassen's algorithm in the proofs of Lemmas 3.3 and 4.3 in the regime $d \le n, m$.
--
--   **Formalization Note** At $d = 0$ the product is zero, and the output cells already hold $0$.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Notation, p.4; proof of Lemma 3.3, p.8

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Rectangular integer matrix multiplication**, as a problem of the published word RAM.
Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256
6bd5cf5d…7730), Section 2, p.4 ("MM(a, b, c) for the time to multiply an a × b by a b × c matrix")
and the proof of Lemma 3.3, p.8 ("MM(n, d, m) = O(nm d^{0.81}) whenever d ≤ n, m").

An instance at scale `s` is `⟨n, m, d, _, X, Y⟩` with `d ≤ n ≤ s`, `d ≤ m ≤ s`, an `n × d`
integer matrix `X` and a `d × m` integer matrix `Y`. The input is `n, m, d`, then `X` and `Y` row by
row; the program must write the `n · m` entries of `X Y` row by row after the input.

**Formalization Note.** The scale `s` fixes the word size and the integer bound of
`SolvedWithin`. At `d = 0` the product is zero, and the output cells already hold `0`. -/
def matMul : Problem where
  Instance s := Σ' (n m d : ℕ) (_ : d ≤ n ∧ d ≤ m ∧ n ≤ s ∧ m ≤ s),
    Matrix (Fin n) (Fin d) ℤ × Matrix (Fin d) (Fin m) ℤ
  input x := [(x.1 : ℤ), x.2.1, x.2.2.1] ++
    (List.ofFn fun i => List.ofFn fun j => x.2.2.2.2.1 i j).flatten ++
    (List.ofFn fun i => List.ofFn fun j => x.2.2.2.2.2 i j).flatten
  output x f := ∀ (i : Fin x.1) (j : Fin x.2.1),
    f (i * x.2.1 + j) = (x.2.2.2.2.1 * x.2.2.2.2.2) i j

end HypercliqueFalse


