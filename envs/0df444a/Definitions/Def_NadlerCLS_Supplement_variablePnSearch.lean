-- Prove2me | Definitions.Def_NadlerCLS_Supplement_variablePnSearch
-- name    : NadlerCLS_Supplement_variablePnSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:54:59.45559+00:00
-- url     : https://prove2.me/theorems/c2557ddf-c82c-4b2d-b288-dd40ef97f2cc
-- title:
--   Polynomial-dimensional $\beta$-Projected-Nadler
-- statement:
--   The polynomial-dimensional form of $\beta$-Projected-Nadler is the disjoint union, over all dimensions $n$, of the published search problems `pnSearch n β`. An input begins with a dimension tag $n$ and then contains a valid $n$-dimensional $\beta$-Projected-Nadler instance; its answers are exactly the published output types (N1)–(N4) for that instance.
--
--   This aggregate is the target of Theorem 5.1, where the reduction constructs dimension $q=d_{\mathrm{emb}}|V|$. It is not the fixed three-dimensional target used to define the canonical CLS problem in Theorem 3.2.
--
--   **Formalization Note** The dimension is encoded with the public self-delimiting natural-number code. The payload and answer relation are reused unchanged from `pnSearch`.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Theorem 5.1, p.14; proof pp.57–58

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_pnSearch

set_option autoImplicit false

namespace NadlerCLS

namespace Supplement

open NetworkEquilibriumCLS.LinearNash

/-- The polynomial-dimension version of `β`-Projected-Nadler used in Theorem 5.1: the
dimension is tagged in the input and the payload is an instance of the published `pnSearch n β`.
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485, Theorem 5.1, p.14, and proof, pp.57–58.)

**Formalization Note** The target dimension is part of the encoded instance and is not fixed to
the three-dimensional CLS target of Theorem 3.2.  The answer relation is exactly the published
`PNAnswer` relation through `pnSearch`; no answer type or promise is changed. -/
def variablePnSearch (β : ℚ) : SearchProblem where
  valid s := ∃ (n : ℕ) (u : List Bool), (pnSearch n β).valid u ∧ s = encNat n ++ u
  answer s t := ∃ (n : ℕ) (u : List Bool), s = encNat n ++ u ∧ (pnSearch n β).answer u t

end Supplement

end NadlerCLS


