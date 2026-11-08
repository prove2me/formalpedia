-- Prove2me | Definitions.Def_AddXnor_chain
-- name    : AddXnor_chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:39.685436+00:00
-- url     : https://prove2.me/theorems/5a68b253-9751-4a56-9daa-8aad76ec72ec
-- title:
--   Add/XNOR step, left-to-right chain value $E_A(x)$, and solvability
-- statement:
--   Fix a word width $m$ and write $M = 2^m$. On $m$-bit words $s, a \in \{0, \dots, M-1\}$ there are two operations: addition modulo $M$, and **bitwise XNOR**
--   $$
--   s \odot a = (M - 1) \oplus s \oplus a,
--   $$
--   the complement of the bitwise XOR $s \oplus a$. An operator is coded by a bit: $x_i = 0$ for addition and $x_i = 1$ for XNOR.
--
--   Given words $A_1, \dots, A_N$ and an operator string $x \in \{0,1\}^{N-1}$, the **state sequence** is $S_1 = A_1$ and
--   $$
--   S_{i+1} = \begin{cases} S_i + A_{i+1} \bmod M, & x_i = 0,\\ S_i \odot A_{i+1}, & x_i = 1,\end{cases}
--   $$
--   and the value of the chain is $E_A(x) = S_N$: the expression $(((A_1 O_1 A_2) O_2 A_3) \cdots) O_{N-1} A_N$ evaluated from left to right. The list $A_1, \dots, A_N$ is **solvable** when some operator string makes $E_A(x) = 0$.
--
--   These are the objects of Definition 1: the Add/XNOR problem asks whether a given chain is solvable.
--
--   **Formalization Note** Words are `BitVec m`, on which `+` is addition modulo $2^m$ and `~~~(s ^^^ a)` is exactly $(2^m-1)\oplus s\oplus a$. The operator bit `true` means XNOR. The chain is a left fold starting from $A_1$. The empty list is not solvable, and a one-element list $[a]$ is solvable iff $a = 0$; neither case occurs in the problem, which has at least two operands.
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), Definition 1 and the paragraph after it, p.2 (PDF p.2)

import Mathlib

namespace AddXnor

/-- One step of an Add/XNOR chain on `m`-bit words (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*,
manuscript, sha256 405d6dda…, Definition 1 and the text after it, p.2 (PDF p.2)).

`step o s a` is `s + a` (addition modulo `2^m`) when `o = false`, and the bitwise XNOR
`s ⊙ a = (2^m − 1) ⊕ s ⊕ a` when `o = true`.

**Formalization Note** Words are `BitVec m`; `+` on `BitVec m` is addition modulo `2^m` and
`~~~(s ^^^ a)` is the complement of the XOR on `m` bits, i.e. `(2^m − 1) ⊕ s ⊕ a`. The operator
code is the paper's `x_i`: `false` (0) is addition, `true` (1) is XNOR. -/
def step {m : ℕ} (o : Bool) (s a : BitVec m) : BitVec m :=
  if o then ~~~(s ^^^ a) else s + a

/-- The value of a left-associative Add/XNOR chain (Wang, Lv, Shen, Zhang, manuscript,
sha256 405d6dda…, p.2 (PDF p.2): the state sequence `S₁ = A₁`, `S_{i+1} = S_i + A_{i+1}` or
`S_i ⊙ A_{i+1}`, and `E_A(x) = S_N`).

`chain a₁ [(x₁, A₂), …, (x_q, A_{q+1})]` starts from `a₁` and applies `step x_i` with operand
`A_{i+1}`, from left to right. -/
def chain {m : ℕ} (a₁ : BitVec m) (l : List (Bool × BitVec m)) : BitVec m :=
  l.foldl (fun s p => step p.1 s p.2) a₁

/-- A list of `m`-bit words `A₁, …, A_N` is **solvable** when some operator string
`x ∈ {0,1}^{N−1}` makes the left-to-right chain evaluate to `0` (Wang, Lv, Shen, Zhang,
manuscript, sha256 405d6dda…, Definition 1, equation (1), p.2 (PDF p.2)).

**Formalization Note** The empty list is not solvable; a one-element list `[a]` is solvable iff
`a = 0`. Neither case arises in the balanced problem, which has `n ≥ 2` operands. -/
def Solvable {m : ℕ} : List (BitVec m) → Prop
  | [] => False
  | a :: rest => ∃ x : List Bool, x.length = rest.length ∧ chain a (x.zip rest) = 0

end AddXnor


