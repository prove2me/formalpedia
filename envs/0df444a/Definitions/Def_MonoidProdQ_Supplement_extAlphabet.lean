-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_extAlphabet
-- name    : MonoidProdQ_Supplement_extAlphabet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:09:52.578983+00:00
-- url     : https://prove2.me/theorems/5ce5cbf9-4ff9-4c17-a430-fb928b9d5c91
-- title:
--   Singleton alphabet $A_f$ of the extension monoid
-- statement:
--   For $f:2^U\to O$, the alphabet of the extension monoid $M_f$ consisting of the identity class and the classes of singletons:
--
--   $$A_f=\{[\emptyset]\}\cup\{[\{u\}]:u\in U\}.$$
--
--   Words over $A_f$ list elements of $U$, and their products are the classes of the sets they list.
--
--   **Formalization Note** A finite subset of $M_f$.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 29, p.41

import Definitions.Def_MonoidProdQ_Supplement_ExtMonoid

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 29, p.41: the alphabet
`A_f = {[∅]} ∪ {[{u}] : u ∈ U}` of the extension monoid `M_f`: the identity class and the classes
of the singletons. -/
def extAlphabet {U O : Type*} [Fintype U] [DecidableEq U] [DecidableEq O] (f : Finset U → O) :
    Finset (ExtMonoid f) :=
  insert (Quotient.mk (extEquiv f) ∅)
    (Finset.univ.image fun u : U => Quotient.mk (extEquiv f) ({u} : Finset U))

end MonoidProdQ.Supplement


