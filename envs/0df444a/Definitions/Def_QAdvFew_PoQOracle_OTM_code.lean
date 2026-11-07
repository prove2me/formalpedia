-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_OTM_code
-- name    : QAdvFew_PoQOracle_OTM_code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:51.109612+00:00
-- url     : https://prove2.me/theorems/d8a911e5-f764-4aa3-acfe-480d170ef6b3
-- title:
--   Bit-string code of an oracle Turing machine
-- statement:
--   The bit-string description of an oracle Turing machine: the numbers $k$ and $g$, then every entry of the transition table in lexicographic order, each number written as $1^m0$.
--
--   The code is injective, so at most $2^t$ machines have a code of fewer than $t$ bits, as the paper's union bounds use. It is one fixed explicit encoding; the paper does not fix one.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The bit-string description of an oracle Turing machine (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23): "`(M, x)`
takes less than `t` bits to specify"): the numbers `k`, `g`, then every entry of the transition
table in lexicographic order of `(q, a, b)`, each number in unary `1^m 0` (`encNat`).

**Formalization Note** The description is injective (`k` and `g` fix the table's shape, and every
entry is self-delimiting). It is one fixed explicit encoding; the paper does not fix one. -/
def OTM.code (M : OTM) : Str :=
  encNat M.k ++ encNat M.g ++
    (List.finRange (M.k + 6)).flatMap fun q =>
      (List.finRange (M.g + 3)).flatMap fun a =>
        (List.finRange (M.g + 3)).flatMap fun b =>
          let r := M.δ q a b
          encNat r.1 ++ encNat r.2.1 ++ encNat r.2.2.1 ++ encNat r.2.2.2.1 ++ encNat r.2.2.2.2

end QAdvFew.PoQOracle


