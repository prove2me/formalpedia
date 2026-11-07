-- Prove2me | Definitions.Def_QuasiStrictNE_oracleBits
-- name    : QuasiStrictNE_oracleBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:11.477832+00:00
-- url     : https://prove2.me/theorems/db2e1072-f8b3-4efa-aafd-4fe4d8d0fe14
-- title:
--   Answers of a linear-comparison oracle during a run
-- statement:
--   An **oracle algorithm** interacts with a hidden point $x\in\mathbb R^d$ only through queries "is $a^\top x\le b$?" with rational $a,b$; each query may depend on the answers to previous ones. Formally the algorithm is a function that reads the instance $I$ and the list of answers received so far and returns either a query or a final output. This definition records the list of answers after $r$ rounds: while the algorithm asks a query $(a,b)$, the oracle appends the bit $[a^\top x\le b]$; once it outputs, the list no longer changes.
--
--   **Formalization Note** The pair (instance, answers) is coded as in the public `CardinalMatching.SearchReduces`. A query is the tag `true` followed by `encRatVec d a ++ encRat b`; a string that is not such a code is answered `false`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 6.3, p.9

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix

namespace QuasiStrictNE

open QAlgorithms.LocalHamiltonian

open Classical in
/-- **The answers of a linear-comparison oracle during a run** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 6.3, p.9: "a
polynomial-time algorithm that interacts with a linear-comparison oracle for the point x. Each query
asks whether a⊤x ≤ b with rational input a and b, and may depend on the answers to previous
queries").

An oracle algorithm is a function `step` that reads the instance `I` and the list of oracle answers
received so far (as the pair code `I # answers`) and returns either a query, tagged `true`, or a
final output, tagged `false`. `oracleBits step I x r` is the list of answers after `r` rounds when the
hidden point is `x ∈ ℝ^d`: in each round, if `step` returns `true :: code`, the oracle appends the bit
"`code` is the code `encRatVec d a ++ encRat b` of a query `(a, b)` with `a⊤x ≤ b`"; if `step`
returns a final output, the list no longer changes.

**Formalization Note** The pair `(I, answers)` is written as in the public
`CardinalMatching.SearchReduces`: `I.map (some ∘ inl) ++ none :: answers.map (some ∘ inr)`. Queries
are coded with the public self-delimiting `encRatVec`/`encRat`, so a code names at most one query; a
string that is not the code of a query of dimension `d` is answered `false`. -/
noncomputable def oracleBits {d : ℕ} (step : List (Option (Bool ⊕ Bool)) → List Bool)
    (I : List Bool) (x : Fin d → ℝ) : ℕ → List Bool
  | 0 => []
  | r + 1 =>
    match step (I.map (some ∘ Sum.inl) ++ none :: (oracleBits step I x r).map (some ∘ Sum.inr)) with
    | true :: code => oracleBits step I x r ++
        [decide (∃ (a : Fin d → ℚ) (b : ℚ), code = CardinalMatching.encRatVec d a ++ encRat b ∧
          ∑ i, (a i : ℝ) * x i ≤ (b : ℝ))]
    | _ => oracleBits step I x r

end QuasiStrictNE


