-- Prove2me | Definitions.Def_KarpLiptonOM_PolyPred2
-- name    : KarpLiptonOM_PolyPred2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:14.49621+00:00
-- url     : https://prove2.me/theorems/e1e70c73-3e6e-400c-9561-3c51a4308e54
-- title:
--   Polynomial-time binary predicate $V(u, w)$
-- statement:
--   A binary predicate $V(u, w)$ on binary strings is **polynomial-time** if the set of encodings $u\#w$ of the pairs with $V(u, w) = 1$ is decidable in polynomial time. Languages of pairs, such as decoders $D(x, a)$ and ONP verifiers $V(x, w)$, are binary predicates of this kind.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (polynomial-time predicates; pairs)

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred

namespace KarpLiptonOM

/-- A binary predicate `V(u, w)` on strings is polynomial-time (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20): `PolyPred` with
`k = 2`, the input being `u#w`. -/
def PolyPred2 (V : List Bool → List Bool → Prop) : Prop :=
  PolyPred 2 (fun l => ∃ u w, l = [u, w] ∧ V u w)

end KarpLiptonOM


