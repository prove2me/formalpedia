-- Prove2me | Definitions.Def_ChapterShiftedQuadraticDegenerate
-- name    : ChapterShiftedQuadraticDegenerate
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T09:03:57.623976+00:00
-- url     : https://prove2.me/theorems/3a3f3378-3e49-4fda-89e3-b688d14ae31c
-- title:
--   Chapter ShiftedQuadraticDegenerate
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterShiftedQuadraticDegenerate.lean`): generated def bundle for ChapterShiftedQuadraticDegenerate. See BookProof/ChapterShiftedQuadraticDegenerate.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedQuadraticDegenerate.lean

import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# The inhomogeneous quadratic Hamiltonian with a **singular** quadratic form

`BookProof.ChapterShiftedQuadraticMatrixEsa` proves that for every real symmetric
**invertible** `A` and arbitrary real `b, b'` the operator

`H = ∑_{p,q} A_{pq}(π_pπ_q + x_px_q/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`,  `πᵢ = −i∂/∂xᵢ`,

is essentially self-adjoint on the translated, modulated Gauss–polynomial core `D_{a,k}`
with `a = −2A⁻¹b`, `k = −A⁻¹b'/2`.  Invertibility was used exactly once: to solve the
*classical equilibrium equations* `A a = −2b`, `A k = −b'/2`.  This module removes it.

The completion of the square only needs a *solution* of those two linear systems, not
uniqueness, so the natural hypothesis is solvability, and for a symmetric `A` solvability
is exactly orthogonality to the kernel:

* `equilibrium_orthogonal_to_kernel` — if `A a = w` then `w ⊥ ker A` (necessity; uses only
  symmetry of `A`);
* `exists_equilibrium` — conversely, if `w ⊥ ker A` then `A a = w` is solvable
  (sufficiency; proved from the spectral theorem for real symmetric matrices in the form
  `BookProof.QuadraticRotation.exists_rotConj_eigenvalues`, by inverting `A` on the
  non-degenerate eigendirections);
* `exists_equilibrium_iff` — the two together.

The consequences, for an **arbitrary** real symmetric `A` (invertible or not, of arbitrary
signature — elliptic, hyperbolic or degenerate):

* `shiftedHMatOp_symmetric_of_equilibrium`,
  `shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium` — symmetry and essential
  self-adjointness on `D_{a,k}` for *any* solution `a, k` of the equilibrium equations;
* `exists_shiftedHMat_esa_of_kernel_orthogonal` — the headline in intrinsic form: if `b`
  and `b'` are orthogonal to `ker A`, a core exists on which `H` is symmetric,
  essentially self-adjoint and generates a complete unitary flow;
* `diagonal_degenerate_essentiallySelfAdjoint` — the concrete diagonal instance
  `∑ᵢ (cᵢ(πᵢ² + xᵢ²/4) + bᵢxᵢ + b'ᵢπᵢ)` with *some weights allowed to vanish*, provided the
  first-order coefficients vanish in the degenerate directions; this is exactly the case
  excluded by `BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint`, which
  requires `cᵢ ≠ 0` for every `i`.

Finally the dynamics is made explicit, by feeding the Hermite eigenbasis into
`BookProof.StoneEigenflow`:

* `exists_shiftedHMat_diagonal_flow` — the unitary flow acts on the translated, modulated,
  rotated Hermite function `ψ_α` by the phase `e^{−iE_αt}`,
  `E_α = ∑ᵢ cᵢ(αᵢ + ½) + const`;
* `exists_shiftedH_diagonal_flow` — the same for the diagonal Hamiltonian of
  `BookProof.ShiftedQuadratic`.

## Honest boundary

Orthogonality of `b, b'` to `ker A` is *necessary* for this route and is not a technical
artefact of the proof: in a kernel direction the Hamiltonian degenerates to the first-order
operator `bᵢxᵢ + b'ᵢπᵢ`, which has no eigenvector in `L²` and is not diagonal in any
Hermite-type basis.  That case (free motion / a constant force in a null direction) is not
covered here.  Nothing here claims a general Faris–Lavine potential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedQuadraticDegenerate

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. Solvability of the classical equilibrium equations -/







/-! ## 2. Symmetry and essential self-adjointness for an arbitrary symmetric `A` -/







/-! ## 3. The concrete degenerate diagonal case -/

/-- The equilibrium vector of a diagonal quadratic form, with the degenerate directions
set to zero. -/
def diagShiftVec (c w : Fin d → ℝ) : Vd d :=
  (WithLp.toLp 2 (fun i => if c i = 0 then 0 else w i / c i) : Vd d)





/-! ## 4. Explicit dynamics on the Hermite eigenbasis -/





end

end BookProof.ShiftedQuadraticDegenerate


