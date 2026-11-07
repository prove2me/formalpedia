-- Prove2me | Definitions.Def_KarpLiptonOM_PolyPred3
-- name    : KarpLiptonOM_PolyPred3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:00.083431+00:00
-- url     : https://prove2.me/theorems/a82f7ce3-575a-49a3-8d8e-8922da477817
-- title:
--   Polynomial-time ternary predicate $V(x, u, w)$
-- statement:
--   A ternary predicate $V(x, u, w)$ on binary strings is **polynomial-time** if the set of encodings $x\#u\#w$ of the triples with $V(x, u, w) = 1$ is decidable in polynomial time. Merlin–Arthur verifiers $V(x, y, r)$ and the order predicates $V(x, u, w)$ of $\mathrm{L}^{\mathrm P}_2$ are of this kind.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (polynomial-time predicates)

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred

namespace KarpLiptonOM

/-- A ternary predicate `V(x, u, w)` on strings is polynomial-time (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20): `PolyPred`
with `k = 3`, the input being `x#u#w`. -/
def PolyPred3 (V : List Bool → List Bool → List Bool → Prop) : Prop :=
  PolyPred 3 (fun l => ∃ u v w, l = [u, v, w] ∧ V u v w)

end KarpLiptonOM


