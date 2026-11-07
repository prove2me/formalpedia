-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Oracle
-- name    : QAdvFew_PoQOracle_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:53.909001+00:00
-- url     : https://prove2.me/theorems/9e31f8b7-32df-4fe5-8fe4-03cd6547dee6
-- title:
--   Classical oracle
-- statement:
--   A **classical oracle** is a function $O : \{0,1\}^* \to \{0,1\}$ on bit strings. A language $L \subseteq \{0,1\}^*$ is identified with its characteristic function, so languages and oracles are the same objects.
--
--   This is the type over which the paper's relativized classes, and its main existential statement, range.
--
--   **Formalization Note** An oracle with several output bits, such as the field-valued $A_t(d,x)$ of §4.1, is queried one output bit at a time, with the index of the bit as part of the query.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.2, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A classical oracle (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, §3.2.2, p. 12 (PDF p. 14): "A classical oracle is a function `f`
on bit strings"; §3.2.3: a language `L ⊆ {0,1}*` is identified with its characteristic function).

**Formalization Note** An oracle with several output bits (the field-valued `A_t(d, x)` of §4.1) is
queried one output bit at a time; the index of the bit is part of the query. -/
abbrev Oracle := Str → Bool

end QAdvFew.PoQOracle


