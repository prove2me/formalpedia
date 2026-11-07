-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_codePair
-- name    : QAdvFew_PoQOracle_codePair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:04.868442+00:00
-- url     : https://prove2.me/theorems/40aa156d-c5a7-4086-8132-0c8874eff539
-- title:
--   Code of a pair $(M,x)$
-- statement:
--   The description $|M,x|$ of a machine and an input is the tuple encoding of the code of $M$ and the string $x$. "$(M,x)$ takes less than $t$ bits to specify" says that this string has length less than $t$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24); proof of Lemma 4.2

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM_code
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The description of a pair `(M, x)` of a machine and an input (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, pp. 21–22
(PDF pp. 23–24): "`(M, x)` takes less than `t` bits to specify"; proof of Lemma 4.2: "`|M, x|` is the
number of bits needed to specify `M` and `x`"): the tuple encoding of the machine's code and `x`. -/
def codePair (M : OTM) (x : Str) : Str := tup [M.code, x]

end QAdvFew.PoQOracle


