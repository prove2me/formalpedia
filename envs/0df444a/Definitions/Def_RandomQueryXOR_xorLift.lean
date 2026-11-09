-- Prove2me | Definitions.Def_RandomQueryXOR_xorLift
-- name    : RandomQueryXOR_xorLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:09.973201+00:00
-- url     : https://prove2.me/theorems/13f5c624-01b6-40b0-83bb-79ed54739003
-- title:
--   XOR-function $g = f\circ\oplus_2$
-- statement:
--   For a base function $f:\{0,1\}^n\to\{0,1\}$, the **XOR-function** $g=f\circ\oplus_2:\{0,1\}^{2n}\to\{0,1\}$ applies $f$ to the parities of the $n$ consecutive pairs of input bits:
--   $$
--   g(y)=f\bigl(y(1)\oplus y(2),\ y(3)\oplus y(4),\ \dots,\ y(2n-1)\oplus y(2n)\bigr).
--   $$
--   This class contains equality and Hamming-distance functions; Result 1 bounds the time-space complexity of every such $g$ in the random query model in terms of its sensitivity.
--
--   **Formalization Note** $[2n]$ is `Fin (2 * n)`, 0-based: the paper's pair $(2i-1,2i)$, $i\in[n]$, is $(2i,2i+1)$ for `i : Fin n` (`pairFst i`, `pairSnd i`).
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §1, p.2 (PDF p.4); pairing displayed p.30 (PDF p.32)

import Mathlib

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

/-- The first index `2i − 1` of the `i`-th pair of `[2n]` (0-based: index `2i` of
`Fin (2 * n)` for `i : Fin n`). -/
def pairFst {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by omega⟩

/-- The second index `2i` of the `i`-th pair of `[2n]` (0-based: index `2i + 1` of
`Fin (2 * n)` for `i : Fin n`). -/
def pairSnd {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩

/-- The XOR-function `g = f ∘ ⊕2 : {0,1}^{2n} → {0,1}` of a base function `f : {0,1}^n → {0,1}`,
`g(y) = f(y(1) ⊕ y(2), y(3) ⊕ y(4), …, y(2n − 1) ⊕ y(2n))` (Garg, Sundaresan, Velusamy,
*XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, §1, p.2 = PDF p.4,
pairing displayed on p.30 = PDF p.32).

**Formalization Note** `[2n]` is `Fin (2 * n)`, 0-based: the paper's pair `(2i − 1, 2i)` for
`i ∈ [n]` is `(pairFst i, pairSnd i) = (2i, 2i + 1)` for `i : Fin n`. -/
def xorLift {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin (2 * n) → Bool) → Bool :=
  fun y => f fun i => xor (y (pairFst i)) (y (pairSnd i))

end RandomQueryXOR


