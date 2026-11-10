-- Prove2me | Definitions.Def_AvgWorstGap_MINKT
-- name    : AvgWorstGap_MINKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:49:12.599791+00:00
-- url     : https://prove2.me/theorems/c133b36f-c8fd-4b02-bf78-aa75f4a417f5
-- title:
--   The language $\mathrm{MINKT}^O$
-- statement:
--   For an oracle $O$,
--   $$\mathrm{MINKT}^O:\quad \mathrm{YES}=\{(x,1^s,1^t) : K^{t,O}(x)\le s\},\qquad \mathrm{NO}=\{(x,1^s,1^t) : K^{t,O}(x)>s\}.$$
--   Since YES and NO together cover every instance, $\mathrm{MINKT}^O$ is a language. As a set of strings it is the set of YES instances.
--
--   **Formalization Note** Instances use the tuple encoding. Strings that are not instances are not in the language.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.5, p.14

import Mathlib
import Definitions.Def_AvgWorstGap_Kt
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_AvgWorstGap_pairStr

namespace AvgWorstGap

open NKtLB

/-- **`MINKT^O`** (Def. 2.5, arXiv:2610.19162, version of October 30, 2026, p.14): "For an oracle
`O`, we define the promise language `MINKT^O ≜ (YES, NO)` as `YES = { (x, 1^s, 1^t) | K^{t,O}(x) ≤
s }`, `NO = { (x, 1^s, 1^t) | K^{t,O}(x) > s }`."

**Formalization Note.** YES ∪ NO is every instance, so `MINKT^O` is a language; it is the set of
YES instances, with `(x, 1^s, 1^t)` encoded by `tupleEnc`. Strings that are not instances are not in
the language. -/
def MINKT (O : Set (List Bool)) : Set (List Bool) :=
  {z | ∃ (x : List Bool) (s t : ℕ), z = tupleEnc [x, unary s, unary t] ∧ Kt O t x [] [] ≤ (s : ℕ∞)}

end AvgWorstGap


