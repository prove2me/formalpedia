-- Prove2me | Definitions.Def_SeededShannon_Supplement_symCode
-- name    : SeededShannon_Supplement_symCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:43:05.133395+00:00
-- url     : https://prove2.me/theorems/afface03-e4e1-4fb7-8824-61b67ecf96ae
-- title:
--   Binary codes of symbols, words and lists over an alphabet of size $q$
-- statement:
--   The list-recovery theorems of Appendix C are statements about algorithms, so their inputs and outputs are bit strings. A symbol of an alphabet of size $q$ (an element of $\mathbb F_q$, named by $\{0,\dots,q-1\}$) is written in binary with $\lceil\log_2(q+1)\rceil$ digits; a word is the tuple of its symbol codes; a pair of symbols is the concatenation of their codes; a collection of lists $T_i$ is the tuple of the tuples of the codes of the elements of each list, in increasing order.
--
--   **Formalization Note** The field structure of $\mathbb F_q$ does not enter Theorems C.4 and C.6, which only use $\mathbb F_q$ as an alphabet and an index set; any representation of $\mathbb F_q$ is in polynomial-time bijection with this one.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Appendix C, pp.65–68 (PDF pp.68–71)

import Mathlib
import Definitions.Def_KarpLiptonOM_binW
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace SeededShannon.Supplement

/-- The binary code of a symbol of an alphabet of size `q` (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Appendix C, pp.65–68: codes over `𝔽_q`), given as
an element of `Fin q`, with `⌈log₂(q + 1)⌉` binary digits.

**Formalization Note** The field `𝔽_q` enters Theorems C.4 and C.6 only as an alphabet of size `q`
(and as the index set of the coordinates in C.6); its elements are named by `Fin q`. -/
def symCode (q : ℕ) (a : Fin q) : List Bool := KarpLiptonOM.binW (Nat.size q) a.val

/-- The code of a word over `Fin q`: the tuple of its symbol codes. -/
def wordCode {n q : ℕ} (c : Fin n → Fin q) : List Bool :=
  QAdvFew.PoQOracle.tup (List.ofFn (fun i => symCode q (c i)))

/-- The code of a word over `Fin q × Fin q` (pairs of symbols). -/
def pairWordCode {n q : ℕ} (c : Fin n → Fin q × Fin q) : List Bool :=
  QAdvFew.PoQOracle.tup (List.ofFn (fun i => symCode q (c i).1 ++ symCode q (c i).2))

/-- The code of a collection of lists `T_i ⊆ Fin q`, `i < n`: the tuple of the tuples of the
codes of the elements of each list, in increasing order. -/
def listsCode {n q : ℕ} (T : Fin n → Finset (Fin q)) : List Bool :=
  QAdvFew.PoQOracle.tup (List.ofFn (fun i =>
    QAdvFew.PoQOracle.tup (((List.finRange q).filter (fun a => a ∈ T i)).map (symCode q))))

/-- The code of a collection of lists `U_x ⊆ Fin q × Fin q`, `x < n`: for each `x`, the tuple of
the codes `code(a) ‖ code(b)` of the pairs `(a, b) ∈ U_x`, in lexicographic order. -/
def pairListsCode {n q : ℕ} (U : Fin n → Finset (Fin q × Fin q)) : List Bool :=
  QAdvFew.PoQOracle.tup (List.ofFn (fun i =>
    QAdvFew.PoQOracle.tup ((List.finRange q).flatMap (fun a => (List.finRange q).filterMap
      (fun b => if (a, b) ∈ U i then some (symCode q a ++ symCode q b) else none)))))

end SeededShannon.Supplement


