-- Prove2me | Definitions.Def_RvsCert_Idx
-- name    : RvsCert_Idx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:42.028148+00:00
-- url     : https://prove2.me/theorems/47c1321a-5de3-47d0-842a-7e8beda594d3
-- title:
--   Input bits of the champion function
-- statement:
--   The input of the function is a bit string $(X,Y)$. Its bits are of two kinds:
--
--   1. bit $t<w_X(n)$ of position $p<n$ of the result list $X_{\{c,d\}}$ of a race $\{c,d\}$ (positions $0$-based);
--   2. bit $t<w_Y(n)$ of entry $j<2n-1$ of the proposal card $Y^{(c,b)}$ of athlete $(c,b)$, where $c\in\{0,\dots,2n-1\}$ is the country and $b\in\{0,\dots,n-1\}$ the bib number.
--
--   So the input has $n(2n-1)\cdot n\cdot w_X(n)+2n^2(2n-1)\cdot w_Y(n)=O(n^3\log n)$ bits.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, Formal definition, p.2

import Mathlib
import Definitions.Def_RvsCert_Race
import Definitions.Def_RvsCert_wX
import Definitions.Def_RvsCert_wY

namespace RvsCert

/-- **Input bit positions of the function** (Formal definition, Section 2, p.2 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "The input to f is (X, Y), where both X and Y are bit strings"). A bit
is either
* `Sum.inl (r, p, t)`: bit `t` of position `p` (`0`-based, `p < n`) of the result list `X_r` of
  race `r`; or
* `Sum.inr ((c, b), j, t)`: bit `t` of entry `j` (`j < 2n − 1`) of the proposal card `Y^{(c,b)}`
  of athlete `(c, b)`, country `c : Fin (2n)`, bib `b : Fin n`.

**Formalization Note.** Fixed-width binary encoding: `wX n` bits per race entry, `wY n` bits per
card entry. -/
abbrev Idx (n : ℕ) : Type :=
  (Race n × Fin n × Fin (wX n)) ⊕ ((Fin (2 * n) × Fin n) × Fin (2 * n - 1) × Fin (wY n))

end RvsCert


