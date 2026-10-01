-- Prove2me | Definitions.Def_ChapterSymmetryEntropy
-- name    : ChapterSymmetryEntropy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:44:51.081144+00:00
-- url     : https://prove2.me/theorems/7f1a8f0a-6e63-426e-a5fd-4b505c4f67b3
-- title:
--   Chapter SymmetryEntropy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSymmetryEntropy.lean`): generated def bundle for ChapterSymmetryEntropy. See BookProof/ChapterSymmetryEntropy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSymmetryEntropy.lean

import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Mathlib


/-!
# Symmetries as irreversible processes: a non-deterministic symmetry raises the entropy

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated
quantum system"*, §*"Symmetries as irreversible processes"* (`book.tex` line ~2678):

> *"A non-deterministic symmetry transformation, when acting on a deterministic ensemble
> increases the entropy of the ensemble after the wave-function collapse and therefore must
> be an irreversible transformation."*

We formalize exactly that statement in the finite-dimensional Born model already used by
`BookProof.ChapterReconstruct` (which proves that a symmetry acts on probability
distributions iff it is *deterministic*, i.e. each column of `U` has at most one nonzero
entry) and with the Shannon entropy of `BookProof.ChapterMarkovEntropy`.

A *deterministic ensemble* is a point mass `δ_a`: the system is known to be in the basis
state `a`.  Acting with the symmetry `U` and collapsing the wave-function produces the Born
distribution of the `a`-th column,

```
bornCol U a k = ‖U k a‖² ,
```

a probability vector because the column of a unitary matrix is a unit vector.  The initial
entropy is `0` (`entropy_pointMass`), so "the entropy increases" means exactly
`0 < entropy (bornCol U a)`, and the theorem is that this happens **iff** the symmetry is
non-deterministic in that column.

## Main results

* `entropy_nonneg` — the Shannon entropy of a sub-probability vector is nonnegative.
* `entropy_eq_zero_iff` — it vanishes iff every entry is `0` or `1`.
* `entropy_pointMass` — a deterministic ensemble has zero entropy.
* `isDeterministicCol_iff_entropy_eq_zero` — for a unit column, determinism of the symmetry
  is equivalent to the collapsed ensemble still having zero entropy.
* `entropy_bornCol_pos_iff_not_isDeterministicCol` — **the headline**: the entropy strictly
  increases iff the symmetry is non-deterministic.
-/

namespace BookProof.SymmetryEntropy

open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

/-! ## Elementary facts about the Shannon entropy -/









/-! ## The Born distribution of a column -/

/-- The distribution obtained by letting the symmetry `U` act on the deterministic
ensemble `δ_a` and collapsing the wave-function: the Born law of the `a`-th column. -/
noncomputable def bornCol (U : Fin n → Fin n → ℂ) (a : Fin n) : Fin n → ℝ :=
  fun k => ‖U k a‖ ^ 2







/-! ## Determinism versus entropy -/









end BookProof.SymmetryEntropy


