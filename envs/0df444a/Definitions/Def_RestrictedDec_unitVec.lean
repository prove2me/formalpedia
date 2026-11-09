-- Prove2me | Definitions.Def_RestrictedDec_unitVec
-- name    : RestrictedDec_unitVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:59.548342+00:00
-- url     : https://prove2.me/theorems/edbfa19c-0491-45c4-ae76-a4567b892691
-- title:
--   The messages $0^n$, $e_k$ and the least position of a set
-- statement:
--   For $n\in\mathbb N$ write $0^n\in\{0,1\}^n$ for the all-zero message and, for a position $k\in[n]=\{1,\dots,n\}$, $e_k\in\{0,1\}^n$ for the message with a single $1$ in position $k$. For a finite set $s$ of positions, $\min s$ is its least element.
--
--   These are the messages used by the two constructions and the two attacks in the proof of Corollary 2, which choose "uniformly in $\lambda$" positions $i\in S_\lambda$ and $j\in T_\lambda\setminus S_\lambda$.
--
--   **Formalization Note** Positions are numbered from $1$; position $k$ is list index $k-1$. For $k=0$ (or $k>n$) there is no such position and $e_k=0^n$, and the least element of the empty set is $0$: these are the default choices at security parameters where the paper's position does not exist.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22; §1.2, p.9 ([n] = {1, …, n})

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The all-zero message `0ⁿ ∈ {0,1}ⁿ`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22
("Write 0n for the all-zero message"). -/
def zeros (n : ℕ) : Str := List.replicate n false

/-- The unit message `e_k ∈ {0,1}ⁿ` with a single `1` in position `k`, positions numbered
`1, …, n` as in `[n] = {1, …, n}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22
("ek for the message with a single 1 in position k"); §1.2, p.9 ("[n] = {1, . . . , n}").

**Formalization Note.** Position `k` is list index `k − 1`. For `k = 0` or `k > n` there is no
such position and `unitVec n k = 0ⁿ`; the constructions use this as their default at security
parameters where the chosen position does not exist. -/
def unitVec (n k : ℕ) : Str := (List.range n).map fun r => decide (r + 1 = k)

/-- The least element of a finite set of positions, and `0` (no position) for the empty set.
Used to "choose, uniformly in λ, positions i ∈ Sλ and j ∈ Tλ \ Sλ" (proof of Corollary 2, p.22). -/
def leastIdx (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.min' h else 0

theorem zeros_length (n : ℕ) : (zeros n).length = n := by simp [zeros]

theorem unitVec_length (n k : ℕ) : (unitVec n k).length = n := by simp [unitVec]

end RestrictedDec


