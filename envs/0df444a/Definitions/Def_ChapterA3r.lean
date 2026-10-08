-- Prove2me | Definitions.Def_ChapterA3r
-- name    : ChapterA3r
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:57:38.158611+00:00
-- url     : https://prove2.me/theorems/e6802d1a-b0d2-496b-b972-1f590af5bee1
-- title:
--   Chapter A3r
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3r.lean`): generated def bundle for ChapterA3r. See BookProof/ChapterA3r.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3r.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3p
import Definitions.Def_ChapterA3q
import Mathlib

/-!
# Chapter A, §A.3 — Note 50 / Lemma 52: dimensions of the complete-reducibility
summands (the ranks of the symmetric / antisymmetric / mixed projectors)

Source: `book.tex` §A.3, Note 50 (Weyl complete reducibility) and Lemma 52.

`ChapterA3n`/`ChapterA3o`/`ChapterA3q` built, for arbitrary `N`, the complete
system of pairwise orthogonal idempotent full-Lorentz–invariant projectors
`{projSym N, projAnti N, projMixed N}` realizing
`V^{⊗N} = Sym^N V ⊕ Λ^N V ⊕ (mixed symmetry)`.

Because each of these is an **idempotent** endomorphism of a finite-dimensional
space, its **trace equals its rank**, i.e. the dimension of the summand it
projects onto.  This file computes those traces in the base case `N = 2`
(the tensor square of the `4`-dimensional Dirac spinor `V`), giving the concrete
dimension count

  `dim (V ⊗ V) = 16 = 10 + 6`,   `dim Sym²V = 10`,   `dim Λ²V = 6`,

with the mixed piece vanishing.  Everything is proved **without** the `EXTERNAL`
Weyl hypothesis.

## Deliverables

* `trace_permMat` — the trace of a braiding matrix `permMat σ` is the number of
  index tuples fixed by `σ` (general `N`).
* `trace_projSym_two` — `tr (projSym 2) = 10` (`= dim Sym²V`).
* `trace_projAnti_two` — `tr (projAnti 2) = 6` (`= dim Λ²V`, the Def 57 pair).
* `trace_projMixed_two` — `tr (projMixed 2) = 0` (no mixed piece for `N = 2`).
* `trace_decomposition_two` — the dimension count `10 + 6 + 0 = 16 = dim (V ⊗ V)`.

Everything is `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`), with **no `EXTERNAL` hypothesis**.
-/
namespace BookProof.ChapterA3r

end BookProof.ChapterA3r


