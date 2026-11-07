-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_unpad
-- name    : QAdvFew_PoQOracle_unpad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:07.739862+00:00
-- url     : https://prove2.me/theorems/fc96d5e6-e4ed-4640-a5ea-92bb63de481f
-- title:
--   Removing the padding of a query
-- statement:
--   "We will have $B_t,C_t$ ignore padding": a code $c$ of fewer than $t$ bits is written in $t$ bits as $c\,1\,0^{t-|c|-1}$, and this function removes the trailing $1\,0\cdots0$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Removes the padding `1 0…0` from the end of a string (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, p. 22 (PDF p. 24): "we will
have `B_t, C_t` ignore padding"): a code `c` of length `< t` is written in `t` bits as
`c 1 0^{t−|c|−1}`, and `unpad (c ++ [true] ++ zeros) = c`. -/
def unpad (a : Str) : Str := ((a.reverse.dropWhile (· = false)).drop 1).reverse

end QAdvFew.PoQOracle


