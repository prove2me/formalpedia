-- Prove2me | Definitions.Def_GuardedSSSP_fhat
-- name    : GuardedSSSP_fhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:06.494567+00:00
-- url     : https://prove2.me/theorems/c3b9c736-e2f9-4754-9fec-d040bbe6dd60
-- title:
--   The integer factor evaluator $\widehat f_d(x)$ of (30), and its instrumented routine
-- statement:
--   For an integer scale $x\ge0$ set
--
--   $$a_1=\mathrm{bitlen}(x+1),\qquad a_{i+1}=\mathrm{bitlen}(a_i+3),\qquad b_i=\mathrm{bitlen}(a_i-1),$$
--
--   so that $a_1=\lceil\log_2(x+2)\rceil$, $a_{i+1}=\lceil\log_2(4+a_i)\rceil$ and $b_i=\lceil\log_2a_i\rceil$, with $\mathrm{bitlen}(0)=0$. For a generation $d$ put
--
--   $$Q=\sum_{i=1}^{d}b_i2^{d+1-i}+b_{d+1}+b_{d+2},\qquad p=\big\lceil Q/2^{d+1}\big\rceil,\qquad \widehat f_d(x)=2^p.$$
--
--   The instrumented routine computes the same value with word operations (one loop over $i=1,\dots,d+2$ accumulating $Q$ by Horner's rule, then the ceiling and the power) and also returns the number of word operations and the largest intermediate integer.
--
--   $\widehat f_d$ is how the solver evaluates the factor $f_d$ using integer metadata only.
--
--   **Formalization Note** $\mathrm{bitlen}$ is `Nat.size`. Each addition, subtraction, shift, division and bit length counts as one word operation. $a_0$ is an unused placeholder.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §7.1, display (30), p.16 (PDF p.17)

import Mathlib

namespace GuardedSSSP

/-!
# The integer factor evaluator `f̂_d(x)`, display (30), and its instrumented routine

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §7.1, display (30), p.16 (PDF p.17): "For an integer scale
x ≥ 0, set a₁ = ⌈log₂(x + 2)⌉, a_{i+1} = ⌈log₂(4 + a_i)⌉, b_i = ⌈log₂ a_i⌉. All these are exact integer
bit-length operations: a₁ = bitlen(x + 1), a_{i+1} = bitlen(a_i + 3), and b_i = bitlen(a_i − 1), with
bitlen(0) = 0. For requested generation d, form
Q = ∑_{i=1}^{d} b_i 2^{d+1−i} + b_{d+1} + b_{d+2}, p = ⌈Q/2^{d+1}⌉, f̂_d(x) = 2^p."

* `aSeq x i`, `bSeq x i`, `Qnum d x`, `pexp d x`, `fhat d x` are these quantities, written directly from (30).
* `fhatRun d x` is the routine that computes them with word operations, instrumented: it returns
  `(value, number of word operations, largest intermediate integer)`.

**Formalization Note.**
* `bitlen` is `Nat.size`, which has `Nat.size 0 = 0` and `Nat.size k = ⌈log₂(k + 1)⌉`. Since `a_i ≥ 1`,
  `a_i − 1` is never a truncated subtraction. `aSeq x 0 = 0` is an unused placeholder.
* `⌈Q/D⌉` is `(Q + D − 1)/D` for `D = 2^{d+1} ≥ 1`.
* `fhatRun` computes `a_i, b_i` for `i = 1, …, d + 2` in one loop. It accumulates
  `Q = 2·(∑_{i≤d} b_i 2^{d−i}) + b_{d+1} + b_{d+2}` by Horner's rule (one doubling shift and one addition
  per step for `i ≤ d + 1`, one addition for `i = d + 2`), then forms `D = 2^{d+1}`, `Q + D`, `Q + D − 1`,
  the quotient `p` and `2^p`. Each addition, subtraction, shift, division and bit length counts one word
  operation. The largest intermediate is the maximum over every integer the routine forms.
-/

/-- `a_i` of (30), for `i ≥ 1`: `a₁ = bitlen(x + 1)`, `a_{i+1} = bitlen(a_i + 3)`. -/
def aSeq (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.size (x + 1)
  | (i + 2) => Nat.size (aSeq x (i + 1) + 3)

/-- `b_i = bitlen(a_i − 1)` of (30). -/
def bSeq (x i : ℕ) : ℕ := Nat.size (aSeq x i - 1)

/-- `Q = ∑_{i=1}^{d} b_i 2^{d+1−i} + b_{d+1} + b_{d+2}` of (30). -/
def Qnum (d x : ℕ) : ℕ :=
  (∑ i ∈ Finset.Icc 1 d, bSeq x i * 2 ^ (d + 1 - i)) + bSeq x (d + 1) + bSeq x (d + 2)

/-- `p = ⌈Q/2^{d+1}⌉` of (30). -/
def pexp (d x : ℕ) : ℕ := (Qnum d x + 2 ^ (d + 1) - 1) / 2 ^ (d + 1)

/-- The integer evaluator `f̂_d(x) = 2^p` of (30). -/
def fhat (d x : ℕ) : ℕ := 2 ^ pexp d x

/-- The loop of the routine after processing indices `1, …, k`: `(a_k, accumulator, word operations,
largest intermediate)`. -/
def fhatLoop (x d : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0)
  | k + 1 =>
    let st := fhatLoop x d k
    let arg := if k = 0 then x + 1 else st.1 + 3
    let a := Nat.size arg
    let am1 := a - 1
    let b := Nat.size am1
    let acc := if k + 1 ≤ d + 1 then 2 * st.2.1 + b else st.2.1 + b
    let ops := st.2.2.1 + 4 + (if k + 1 ≤ d + 1 then 2 else 1)
    (a, acc, ops,
      max st.2.2.2 (max arg (max a (max am1 (max b (max (2 * st.2.1) acc))))))

/-- The instrumented evaluator: `(f̂_d(x), word operations, largest intermediate integer)`. -/
def fhatRun (d x : ℕ) : ℕ × ℕ × ℕ :=
  let st := fhatLoop x d (d + 2)
  let Q := st.2.1
  let D := 2 ^ (d + 1)
  let num := Q + D - 1
  let p := num / D
  (2 ^ p, st.2.2.1 + 5, max st.2.2.2 (max D (max (Q + D) (max num (max p (2 ^ p))))))

end GuardedSSSP


