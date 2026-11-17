-- Prove2me | Definitions.Def_SigmoidWire_Supplement_selFn
-- name    : SigmoidWire_Supplement_selFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:39:57.024197+00:00
-- url     : https://prove2.me/theorems/4ba41946-09b9-465c-a974-2b2b859f4c8c
-- title:
--   The selection function $f_n(x,y)=y_x$ for $n=2^k$
-- statement:
--   Let $n=2^k$. The **selection function** $f_n$ on inputs $x\in\{0,1\}^{k}$ and $y\in\{0,1\}^n$ is
--   $$f_n(x,y)=y_x,$$
--   the entry of $y$ (indexed $0,\dots,n-1$) whose index is the integer with binary representation $x$.
--
--   Every Boolean function on $k$ bits is $f_n(\cdot,y)$ for some $y$, so the functions $f_n(\cdot,y)$ shatter $\{0,1\}^k$; Theorem 6.5 turns this into a gate lower bound.
--
--   **Formalization Note** The input is $x$ followed by $y$ ($k+2^k$ bits). The binary representation is read least significant bit first ($x_j$ has weight $2^j$); the other order gives the same function up to a permutation of the $x$ inputs, which changes neither the size nor the depth of a circuit.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), §6.2, p.40

import Mathlib

namespace SigmoidWire.Supplement

/-- **The selection function `f_n`** for `n = 2^k` (§6.2).

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), §6.2, p.40 (PDF p.42): "We
define the selection Boolean function f_n(x, y) on inputs x ∈ {0,1}^{log n} and y ∈ {0,1}^n, where
f_n(x, y) = y_x is simply the x-th entry of y. Here, we identify x with the integer in
{0, …, n − 1} whose binary representation is x, and index the coordinates of y from 0 to n − 1."
The section assumes that `n` is a power of `2` and takes logarithms in base `2`.

`selFn k` is `f_{2^k}`: an input is `z : Fin (k + 2^k) → Bool`, with `x = (z 0, …, z (k−1))` and
`y_t = z (k + t)` for `t = 0, …, 2^k − 1`, and `selFn k z = y_t` for `t = Σ_{j<k} x_j 2^j`.

**Formalization Note.** The binary representation is read least-significant bit first (`x_j` has
weight `2^j`, via `finFunctionFinEquiv`). The other bit order gives the same function up to a
permutation of the `x` inputs, which changes neither the size nor the depth of a circuit. -/
def selFn (k : ℕ) (z : Fin (k + 2 ^ k) → Bool) : Bool :=
  z (Fin.natAdd k (finFunctionFinEquiv
    (fun j : Fin k => if z (Fin.castAdd (2 ^ k) j) then (1 : Fin 2) else 0)))

end SigmoidWire.Supplement


