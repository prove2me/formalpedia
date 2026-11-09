-- Prove2me | Definitions.Def_ChapterGradedBandSchurEsaPromoted
-- name    : ChapterGradedBandSchurEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T16:32:59.81953+00:00
-- url     : https://prove2.me/theorems/cd93c4a4-9259-41f3-a788-d1cd374ba63e
-- title:
--   Graded band Schur estimates: band-restricted Schur complements and their boundedness
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGradedBandSchurEsa.lean`): the band-graded Schur layer.  The platform's served `Def_ChapterGradedBandSchurEsa` copy is an empty skeleton whose namespace is `BookProof.ChapterGradedBandSchurEsa`, so every consumer statement that says `open BookProof.GradedBandSchur` dies with `unknown namespace`.  Published bundles are immutable, so this bundle re-carries the chapter's DEFINITIONS in the original namespace; its theorem facts stay separate problem nodes.  Consumers add a single `import Definitions.Def_ChapterGradedBandSchurEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGradedBandSchurEsa.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterGradedBandSchurEsa` copy is a
-- skeleton (no declarations at all), so `open BookProof.GradedBandSchur` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterGradedBandSchurEsaPromoted`.
-- Left to the problem nodes on purpose (theorem facts):
--   degW_ge_one
--   degW_pos
--   wRow_of_gradedBand
--   wCol_of_gradedBand
--   wComm_of_gradedBand
--   dGamma_essentiallySelfAdjointOn_core_gradedBand
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib


/-!
# From a graded band matrix to the weighted Schur gates

`BookProof.ChapterFockWeightedSchurEsa` proves essential self-adjointness of `dΓ(A)` on the
finite-occupation core under three gates weighted by a symbol `w ≥ 1` — the row gate, the
column gate and the commutator gate.  This chapter discharges all three from a single
structural hypothesis, the one satisfied by the Hermite matrix of a quadratic Hamiltonian:

```text
(card)  every column has at most `M` nonzero entries;
(band)  `A_{kj} = 0` unless `|deg j − deg k| ≤ D`;
(growth)`|A_{kj}| ≤ C (deg k + 1)`.
```

With the symbol `w k = deg k + 1` (`degW`):

* **`wRow_of_gradedBand`** — the row gate with `K = C·M`;
* **`wCol_of_gradedBand`** — the column gate with the same `K`, by hermiticity;
* **`wComm_of_gradedBand`** — the commutator gate with `B = C·M·D·(D+2)`: the band makes
  `|w_j² − w_k²| / (w_k w_j) ≤ D(D+2)/w_k`, which cancels the growth of the entries;
* **`dGamma_essentiallySelfAdjointOn_core_gradedBand`** — hence `dΓ(A)` is essentially
  self-adjoint on the finite-occupation core.  The one-particle operator need not be
  bounded: only its growth relative to the grading is constrained.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.GradedBandSchur

open BookProof.FockSecondQuantization BookProof.FockSchur BookProof.FockWeightedSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

/-- The symbol attached to a grading: `w k = deg k + 1`. -/
def degW (deg : ℕ → ℕ) : ℕ → ℝ := fun k => (deg k : ℝ) + 1

end

end BookProof.GradedBandSchur


