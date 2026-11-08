-- Prove2me | Definitions.Def_AddXnor_inst
-- name    : AddXnor_inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:57.169771+00:00
-- url     : https://prove2.me/theorems/a35a55fc-d359-4e24-a5da-58340650c65a
-- title:
--   The Subset-Sum to Add/XNOR construction (6)–(8)
-- statement:
--   Let $(s_1, \dots, s_r; T)$ be a Subset-Sum instance and $S = \sum_i s_i$. The construction of the paper sets
--   $$
--   h = \lceil \log_2(S+1) \rceil,\qquad p_i = 2 + 4(i-1)\ (1 \le i \le r),\qquad K = 4r+2,\qquad n = K + h + 1,
--   $$
--   $$
--   C = 1 + \sum_{i=1}^r 2^{p_i},\quad P = C + 2^{K+1}T,\quad U_i = 3\cdot 2^{p_i},\quad V_i = s_i 2^K - U_i,\quad M = 2^n,\quad D = M - P,
--   $$
--   and outputs the sequence of $n$ operands
--   $$
--   \bigl(C,\ U_1, V_1, U_1, V_1,\ \dots,\ U_r, V_r, U_r, V_r,\ \underbrace{0, \dots, 0}_{h+1},\ D\bigr),
--   $$
--   each written as an $n$-bit word. Gadget $i$ is the block $U_i, V_i, U_i, V_i$; bits $p_i, \dots, p_i+3$ form its guard field, and the lowest two bits are control bits.
--
--   This is the instance whose solvability is equivalent to the Subset-Sum instance having a solution (for $r \ge 1$, all $s_i > 0$ and $0 \le T \le S$).
--
--   **Formalization Note** Gadgets are indexed from $0$, so $p_i = 2 + 4i$ for $0 \le i < r$. $h$ is `Nat.size S`, the number of binary digits of $S$, which equals $\lceil\log_2(S+1)\rceil$. $V_i$ and $D$ use natural-number subtraction; under the construction's hypotheses both are positive, so nothing is truncated. `instNat` is the list of natural numbers, `instRest` the operands after $C$ as $n$-bit words, and `inst` the full list of words. With 0-based positions, $w[0] = C$; gadget $i$ occupies $w[1+4i], \dots, w[4+4i]$ with operators $x[4i], \dots, x[4i+3]$; the zeros are $w[4r+1], \dots, w[4r+h+1]$ with operators $x[4r], \dots, x[4r+h]$; and $D = w[n-1]$ with the last operator $x[n-2]$.
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), proof of Theorem 1, "Construction", (6) p.9, (7) and (8) p.10 (PDF pp.9–10)

import Mathlib

namespace AddXnor

/-! The Subset-Sum → Add/XNOR construction (6)–(8) (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*,
manuscript, sha256 405d6dda…, proof of Theorem 1, "Construction", pp.9–10 (PDF pp.9–10)), for a
Subset-Sum instance `(s₁, …, s_r; T)` given as `s : List ℕ` and `T : ℕ`.

**Formalization Note** Gadgets are indexed from `0`: `p_i = 2 + 4i` for `i < r` (the paper's
`p_i = 2 + 4(i − 1)`, `1 ≤ i ≤ r`). `h = ⌈log₂(S + 1)⌉` is `Nat.size S`, the least `k` with
`S < 2^k`. `V_i = s_i 2^K − U_i` and `D = 2^n − P` use natural-number subtraction; the
construction's preamble (`r ≥ 1`, all `s_i > 0`, `T ≤ S`) makes both positive, so nothing is
truncated (see the construction-bounds milestone). With 0-based positions in the list (8), the
operands are `w[0] = C`; gadget `i` is `w[1+4i] … w[4+4i] = (U_i, V_i, U_i, V_i)`, joined by the
operators `x[4i] … x[4i+3]`; the `h + 1` zero operands are `w[4r+1] … w[4r+h+1]`, joined by
`x[4r] … x[4r+h]`; and `D = w[n−1]`, joined by the last operator `x[n−2]`. -/

/-- `S = ∑ s_i`, the total of the Subset-Sum instance. -/
def S (s : List ℕ) : ℕ := s.sum

/-- `h = ⌈log₂(S + 1)⌉`, (6), p.9: the bit length of `S`. -/
def hOf (s : List ℕ) : ℕ := Nat.size (S s)

/-- `K = 4r + 2`, (6), p.9. -/
def KOf (s : List ℕ) : ℕ := 4 * s.length + 2

/-- `n = K + h + 1`, (6), p.9: the number of operands and the word width. -/
def nOf (s : List ℕ) : ℕ := KOf s + hOf s + 1

/-- `p_i = 2 + 4i` (0-based gadget index `i`), (6), p.9. -/
def pOf (i : ℕ) : ℕ := 2 + 4 * i

/-- `C = 1 + ∑_i 2^{p_i}`, (7), p.10. -/
def C (s : List ℕ) : ℕ := 1 + ∑ i ∈ Finset.range s.length, 2 ^ pOf i

/-- `P = C + 2^{K+1} T`, (7), p.10. -/
def P (s : List ℕ) (T : ℕ) : ℕ := C s + 2 ^ (KOf s + 1) * T

/-- `U_i = 3 · 2^{p_i}`, (7), p.10. -/
def U (i : ℕ) : ℕ := 3 * 2 ^ pOf i

/-- `V_i = s_i 2^K − U_i`, (7), p.10 (natural-number subtraction; `s_i` is `s.getD i 0`). -/
def V (s : List ℕ) (i : ℕ) : ℕ := s.getD i 0 * 2 ^ KOf s - U i

/-- `D = M − P` with `M = 2^n`, (7), p.10 (natural-number subtraction). -/
def D (s : List ℕ) (T : ℕ) : ℕ := 2 ^ nOf s - P s T

/-- The operands after `C` in (8), as natural numbers:
`U_0, V_0, U_0, V_0, …, U_{r−1}, V_{r−1}, U_{r−1}, V_{r−1}, 0, …, 0 (h + 1 zeros), D`. -/
def instRestNat (s : List ℕ) (T : ℕ) : List ℕ :=
  (List.range s.length).flatMap (fun i => [U i, V s i, U i, V s i]) ++
    List.replicate (hOf s + 1) 0 ++ [D s T]

/-- The output sequence (8), p.10, as natural numbers:
`(C, U_0, V_0, U_0, V_0, …, U_{r−1}, V_{r−1}, U_{r−1}, V_{r−1}, 0, …, 0, D)`. -/
def instNat (s : List ℕ) (T : ℕ) : List ℕ := C s :: instRestNat s T

/-- The operands after `C` in (8) as `n`-bit words. -/
def instRest (s : List ℕ) (T : ℕ) : List (BitVec (nOf s)) :=
  (instRestNat s T).map (BitVec.ofNat (nOf s))

/-- The output sequence (8), p.10, as a list of `n`-bit words, `n = nOf s`: the first word is
`C`, followed by `instRest s T`. -/
def inst (s : List ℕ) (T : ℕ) : List (BitVec (nOf s)) :=
  BitVec.ofNat (nOf s) (C s) :: instRest s T

end AddXnor


