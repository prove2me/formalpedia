-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_codeBit
-- name    : FoundationsRL_DECExamples_codeBit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:56.687995+00:00
-- url     : https://prove2.me/theorems/5d2981e1-523e-4e6e-ba9e-6ab9853cf77a
-- title:
--   Binary code $b_j(\pi)\in\{0,1\}$ of an action of $[A]$, $A=2^n$
-- statement:
--   Let $A=2^n$. Each action $\pi\in[A]=\{1,\dots,A\}$ has the binary encoding $b(\pi)=(b_1(\pi),\dots,b_n(\pi))\in\{0,1\}^n$ of its index, with $b_1$ the most significant bit: action $1$ has code $(0,\dots,0)$, action $2$ has code $(0,\dots,0,1)$, and so on. This is the code read off by the cheating actions of Example 4.2.
--
--   **Formalization Note** Actions and coordinates are $0$-based: $i:\{0,\dots,2^n-1\}$ is the action $i+1$ and $j:\{0,\dots,n-1\}$ the coordinate $j+1$, and $b_{j+1}(i+1)$ is bit $n-1-j$ of $i$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 4.2, pp. 62–63

import Mathlib

namespace FoundationsRL.DECExamples

/-- The coordinate `b_{j+1} ∈ {0, 1}` of the binary encoding of an action of `[A]`, `A = 2^n`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 4.2, pp. 62–63.

**Formalization Note.** Actions and coordinates are `0`-based: `i : Fin (2 ^ n)` is the action
`i + 1` of the notes and `j : Fin n` is the coordinate `j + 1`. The first coordinate is the most
significant bit, so the action `1` (`i = 0`) has code `(0, …, 0)` and the action `2` (`i = 1`) has
code `(0, …, 0, 1)`, as in the example. -/
def codeBit {n : ℕ} (i : Fin (2 ^ n)) (j : Fin n) : ℝ :=
  if (i : ℕ).testBit (n - 1 - (j : ℕ)) then 1 else 0

end FoundationsRL.DECExamples


