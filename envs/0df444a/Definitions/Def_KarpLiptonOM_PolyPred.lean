-- Prove2me | Definitions.Def_KarpLiptonOM_PolyPred
-- name    : KarpLiptonOM_PolyPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:59.050558+00:00
-- url     : https://prove2.me/theorems/21deb778-4131-42b6-82ac-53da31554f31
-- title:
--   Polynomial-time $k$-ary predicate
-- statement:
--   A predicate $V$ on $k$-tuples of binary strings is **polynomial-time** if some deterministic Turing machine decides, in time polynomial in the input length, whether a given string $u_1\#\cdots\#u_k$ encodes a tuple with $V(u_1, \dots, u_k) = 1$. The verifiers of ONP, prMA and sOprMA, the orders of $\mathrm{L}^{\mathrm P}_2$ and OMIN, the decoders of generator–tester–decoder computations and the predicates of $\Sigma^{\mathrm P}_k$ are all of this kind.
--
--   **Formalization Note** The machine model is the published one-tape Turing machine of `CookPvsNP` (time bound $|w|^c + c$), over the alphabet $\{0, 1, \#\}$ (`Option Bool`); the inputs are the tuple encodings of `tupleEnc`.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (polynomial-time predicates)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- A `k`-ary predicate on binary strings is **polynomial-time** (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20, "definitions
based on polynomial-time predicates"): the language of tuple encodings `u₁#⋯#u_k` of the `k`-tuples
satisfying `V` is in the class `P` of the published Cook model (`CookPvsNP.P`, one-tape Turing
machines running in time `|w|^c + c`), over the alphabet `{0, 1, #}`.

**Formalization Note** `V` is applied only to lists of length exactly `k`; the running time is
polynomial in the total input length `|u₁| + ⋯ + |u_k| + k − 1`. -/
def PolyPred (k : ℕ) (V : List (List Bool) → Prop) : Prop :=
  {s : List (Option Bool) | ∃ l : List (List Bool), l.length = k ∧ V l ∧ s = tupleEnc l}
    ∈ CookPvsNP.P (Option Bool)

end KarpLiptonOM


