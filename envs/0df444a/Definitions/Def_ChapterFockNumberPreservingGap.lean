-- Prove2me | Definitions.Def_ChapterFockNumberPreservingGap
-- name    : ChapterFockNumberPreservingGap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:17:21.433979+00:00
-- url     : https://prove2.me/theorems/a7a1b4d7-9456-4e99-be81-787fc59c1098
-- title:
--   ChapterFockNumberPreservingGap
-- statement:
--   ChapterFockNumberPreservingGap

import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib


/-!
# Chapter FockNumberPreservingGap — the `dΓ` lift beyond the diagonal case

/-!
The final Hamiltonian convention is uniform across QYM, QED, QG, and NS:
the one-particle Hamiltonian is enclosed by outer creation on the left and
outer annihilation on the right. Inner pair terms are retained in the
one-particle operator; the outer annihilator, not an inner normal-ordering
rewrite, proves that the outer vacuum is an exact zero-energy eigenstate.
-/!

`CONSOLIDATED_PLAN.md` (top work package, status update 2026-08-28) lists two remaining
inputs.  The per-order finite certificate is discharged in `ChapterRitzCertificate`; this
chapter weakens the second one as far as it honestly can be weakened.

`ChapterFockOneParticleGap` proves the free `dΓ` lift for a one-particle Hamiltonian
`diagCol e` that is **diagonal** in the chosen occupation-number basis.  That is stronger
than the plan's free/number-preserving hypothesis needs: the lift only requires the
one-particle matrix to be *number preserving* (`dΓ` of a one-particle matrix, i.e. built
from `a†_j a_k`), Hermitian, and to have a **one-particle gap**.  Here the gap is expressed
exactly as it is checked numerically, as positive semidefiniteness of the shifted matrix

  `h − μ ≥ 0`   (`IsPosCol (shiftCol col mu)`),

with no diagonalization and no eigenbasis anywhere.

## Deliverables

* `shiftCol` — the shifted one-particle matrix `h − μ`, and `shiftCol_diagCol` /
  `isPosCol_shiftCol_diagCol`, which show the diagonal case of
  `ChapterFockOneParticleGap` is an instance;
* `creVec_sub`, `dGamma_shiftCol` — `dΓ` is linear in the one-particle matrix:
  `dΓ(h − μ) = dΓ(h) − μN`, the general form of `dGamma_diagCol_shift`;
* `dGamma_vac` — the vacuum is annihilated by `dΓ(h)` for **every** one-particle matrix;
* `number_quadForm_ge` — `⟪u, N u⟫ ≥ ‖u‖²` on vacuum-orthogonal states;
* **`fock_gap_of_number_preserving`** — the lift: if `h − μ ≥ 0` as a one-particle matrix
  and `μ ≥ 0`, then every vacuum-orthogonal finite-particle state has Fock energy at least
  `μ‖u‖²`;
* **`fock_gap_of_number_preserving_op`** — the same statement on the Fock space, with the
  vacuum energy `0`, in the form the Friedrichs machinery consumes.

## Honest boundary

Number preservation is still assumed: everything here is `dΓ` of a one-particle matrix, so
pair creation and other particle-number-changing interactions are **excluded**, exactly as
the plan states.  What is removed is only the diagonal/eigenbasis restriction.  No mass gap
of the physical Yang–Mills Hamiltonian is claimed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.FockNumberPreservingGap

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

/-! ## 1. The shifted one-particle matrix -/

/-- The one-particle matrix `h − μ`, whose positivity is the numerically checked form of
the one-particle gap `h ≥ μ`. -/
def shiftCol (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) : ℕ → (ℕ →₀ ℂ) :=
  fun k => col k - ((mu : ℝ) : ℂ) • Finsupp.single k 1







/-! ## 2. `dΓ` is linear in the one-particle matrix -/









/-! ## 3. The vacuum, and the number operator -/





/-! ## 4. The lift -/





/-! ## 5. The diagonal case is an instance -/



/-! ## 6. From a one-particle *form* gap to the Fock gap

The certificate chain (`ChapterRitzCertificate`, `ChapterBandEnclosure`) delivers a bound of
exactly the shape `⟪x, h x⟫ ≥ μ‖x‖²` on the finite-mode core.  This section consumes it
directly: no eigenbasis, no diagonalization, no boundedness. -/

section FormGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

open BookProof.HermiteGalerkin







end FormGap

end BookProof.FockNumberPreservingGap

end


