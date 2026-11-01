-- Prove2me | Definitions.Def_PacingComplexity_encRatRect
-- name    : PacingComplexity_encRatRect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:33.413988+00:00
-- url     : https://prove2.me/theorems/b7bc4a11-d62b-4140-82ad-612f99a407b3
-- title:
--   Binary encoding of an $n\times m$ rational matrix
-- statement:
--   An $n\times m$ matrix $v$ of rational numbers is encoded as a bit string: $n$ and $m$ in self-delimiting binary, followed by the $nm$ entries in row-major order, each written as a rational number (sign and binary numerator, then binary denominator of the reduced fraction).
--
--   It encodes the values of a pacing game and an allocation. Every code is self-delimiting, so a string encodes at most one matrix.
--
--   **Formalization Note** The paper fixes no encoding; this one is built from the platform's public `encBin` and `encRat`.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, p.3 (rational values and budgets) and p.19 (input size |G|)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace PacingComplexity

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

/-- **Binary encoding of an `n × m` rational matrix**: `n` and `m` in self-delimiting binary
(`encBin`), followed by the `n·m` entries in row-major order, each as a rational (`encRat`: the
sign-and-magnitude binary numerator, then the binary denominator of the reduced fraction).

Used for the value matrix `(vij)` of a second-price pacing game and for an allocation `(xij)`
(Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2,
p.3: "when values and budgets of buyers are rational"; p.19: the input size `|G|` in bits).

**Formalization Note** The paper does not fix an encoding; this one is built from the platform's
public `encBin`/`encRat`, and every code is self-delimiting, so a string encodes at most one
`(n, m, v)`. -/
def encRatRect (n m : ℕ) (v : Fin n → Fin m → ℚ) : List Bool :=
  encBin n ++ encBin m ++
    (List.finRange n).flatMap (fun i => (List.finRange m).flatMap (fun j => encRat (v i j)))

end PacingComplexity


