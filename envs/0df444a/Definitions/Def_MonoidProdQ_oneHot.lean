-- Prove2me | Definitions.Def_MonoidProdQ_oneHot
-- name    : MonoidProdQ_oneHot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:41:55.64716+00:00
-- url     : https://prove2.me/theorems/b329c8ad-de35-48c4-b05b-badac1bbf48d
-- title:
--   One-hot encoding of a letter
-- statement:
--   For a finite alphabet $\Sigma$ and a letter $a\in\Sigma$, the **one-hot code** of $a$ is the vector $e_a\in(\mathbb Z/2)^{\Sigma}$ with a $1$ in coordinate $a$ and $0$ elsewhere. It is the injective encoding through which a quantum query reveals an entire letter: the standard oracle maps $|i,y\rangle$ to $|i,y+e_{x_i}\rangle$.
--
--   **Formalization Note** The paper says that "a query to index $i$ returns the entire element $x_i$ at unit cost" without fixing an encoding. Any two injective encodings give query complexities within a factor of two of each other (query, translate by a fixed reversible lookup, unquery), so statements with universal constants do not depend on the choice. The one-hot code works for every finite alphabet, including the empty one.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Query model, pp.21–22 (encoding choice; cf. proof of Proposition 7, p.22)

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, "Query model", p.21: "A query to index i returns the entire element xᵢ at unit
cost." To feed a letter of a finite alphabet `Sig` to the platform's standard (XOR) oracle,
which adds a value of a finite abelian group to the target register, the letter `a` is encoded
injectively as the one-hot vector `e_a ∈ (ℤ/2)^Sig`.

**Formalization Note.** The paper does not fix an encoding of letters. Any two injective
encodings give query complexities within a factor two of each other (a query in one encoding is
simulated by two in the other: query, translate by a fixed reversible lookup, unquery; cf. the
proof of Proposition 7, p.22), so every `Θ`/`O`/`Ω` statement with universal constants is
unaffected. The one-hot code works for every finite alphabet, including the empty one. -/
def oneHot {Sig : Type*} [DecidableEq Sig] (a : Sig) : Sig → ZMod 2 :=
  Pi.single a 1

end MonoidProdQ


