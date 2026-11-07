-- Prove2me | Definitions.Def_PopRAM_Greedy
-- name    : PopRAM_Greedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:18.287984+00:00
-- url     : https://prove2.me/theorems/99d9ebd5-4b63-4b4c-88b9-833c0a67ad62
-- title:
--   The greedy binary search of U2Bconversion
-- statement:
--   To convert $A=|X_i|<2^{w-1}$ to binary, Protocol 13 processes $\ell=w-2,\dots,0$: it adds the weight $P_\ell$ ($2^\ell$ agents) to an auxiliary set $Z$ and keeps it, writing bit $\ell=1$, if $|Z|\le A$ afterwards; otherwise it removes $P_\ell$ and writes $0$. `greedyZ A w j` is $|Z|$ after the first $j$ iterations, and `greedyBit A w ℓ` is the bit written at position $\ell$:
--   $$b_\ell=[\,Z+2^\ell\le A\,],\qquad Z\leftarrow Z+b_\ell 2^\ell .$$
--
--   **Formalization Note** The majority comparison is taken as exact: this is the deterministic content of the conversion.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §3 technique (4), p.11 (PDF p.12); Protocol 13, p.25 (PDF p.26)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # The greedy binary search of U2Bconversion

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), §3 technique (4), p.11 (PDF p.12), and
Protocol 13, p.25 (PDF p.26): for ℓ = w − 2 down to 0, add the weight P_ℓ (of size 2^ℓ) to Z and keep
it, writing bit ℓ = 1, iff |Z| ≤ |X_i| after the addition; otherwise remove it and write 0.

**Formalization Note** With `A = |X_i|`, `greedyZ A w j` is `|Z|` after the first `j` iterations
(bits `w − 2, …, w − 1 − j`), and `greedyBit A w ℓ` the bit written at `ℓ` (for `ℓ ≤ w − 2`). The
majority comparison is taken as exact (this is the deterministic content of the conversion). -/

/-- `|Z|` after `j` iterations of the loop `ℓ = w − 2, …, 0`. -/
def greedyZ (A w : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      let ℓ := w - 2 - j
      if greedyZ A w j + 2 ^ ℓ ≤ A then greedyZ A w j + 2 ^ ℓ else greedyZ A w j

/-- The bit written at position `ℓ` (iteration `w − 2 − ℓ`). -/
def greedyBit (A w ℓ : ℕ) : Bool :=
  decide (greedyZ A w (w - 2 - ℓ) + 2 ^ ℓ ≤ A)

end PopRAM


