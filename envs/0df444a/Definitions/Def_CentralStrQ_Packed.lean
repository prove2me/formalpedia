-- Prove2me | Definitions.Def_CentralStrQ_Packed
-- name    : CentralStrQ_Packed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:45.238734+00:00
-- url     : https://prove2.me/theorems/ffeb1843-1307-4241-bca5-ae633937b553
-- title:
--   Packed representation $\mathrm{packed}_{w,\sigma}(S)$ of a string
-- statement:
--   Let $w\ge 1$ be the word size and $\sigma\ge 2$ an alphabet size with $\log\sigma\le w$. Put $b=\lceil\log_2\sigma\rceil$ and $s=\lfloor w/b\rfloor$. The **packed representation** of a string $S\in[0\,.\,.\,\sigma)^*$ is the sequence of $k=\lceil |S|/s\rceil$ words $x_1,\dots,x_k$ with
--
--   $$
--   x_i=\sum_{\delta=1}^{\min(s,\,|S|-(i-1)s)} S[(i-1)s+\delta]\cdot 2^{(\delta-1)b}.
--   $$
--
--   So each word except possibly the last stores $s$ symbols of $b$ bits each, the first symbol in the lowest bits, and all unused bits are $0$. A bitvector $B$ is packed as the string over $[0\,.\,.\,2)$ with one $\mapsto 1$ and zero $\mapsto 0$.
--
--   This is the input format of the text and the output format of every bitvector in the mission. For example, with $w=8$ and $\sigma=4$, $\mathrm{packed}_{8,4}(3,1,0,2,3,1)=(135,7)$ (Example 3.5).
--
--   **Formalization Note** Symbols and words are lists of natural numbers, listed from the first. When $b>w$ the definition returns the empty list; this case is excluded by the hypotheses wherever it is used.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Definition 3.3, pp.13–14 (PDF pp.14–15)

import Mathlib

set_option autoImplicit false

namespace CentralStrQ

/-!
# Packed representation of a string (Definition 3.3)

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Definition 3.3, pp.13–14
(PDF pp.14–15): with `b = ⌈log σ⌉` and `s = ⌊w/b⌋`, the packed representation of
`S ∈ [0..σ)*` is the sequence of `k = ⌈|S|/s⌉` words
`x_i = ∑_{δ=1}^{min(s, |S| − (i−1)s)} S[(i−1)s + δ] · 2^{(δ−1)b}`.

**Formalization Note.** Strings over `[0..σ)` are lists of natural numbers; words are listed
0-based (`x_{i+1}` is entry `i`), symbols too. `b = Nat.clog 2 σ` (`= ⌈log₂ σ⌉`). The definition
is meant for `log σ ≤ w`; when `b > w` it returns the empty list (never used so). Unused bits are
`0` automatically (item 5 of the definition). A bitvector `B` is packed as the string over
`[0..2)` with `true ↦ 1`, `false ↦ 0` (`bitsToNat`).
-/

/-- `packed_{w,σ}(S)`. -/
def packed (w σ : ℕ) (S : List ℕ) : List ℕ :=
  let b := Nat.clog 2 σ
  let s := w / b
  (List.range ((S.length + s - 1) / s)).map fun i =>
    ∑ δ ∈ Finset.range (min s (S.length - i * s)), S.getD (i * s + δ) 0 * 2 ^ (δ * b)

/-- A bitvector read as a string over `[0..2)`: `1` for `true`, `0` for `false`. -/
def bitsToNat (B : List Bool) : List ℕ := B.map fun b => if b then 1 else 0

end CentralStrQ


