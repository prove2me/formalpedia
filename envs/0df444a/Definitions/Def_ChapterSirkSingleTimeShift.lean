-- Prove2me | Definitions.Def_ChapterSirkSingleTimeShift
-- name    : ChapterSirkSingleTimeShift
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T13:06:35.680086+00:00
-- url     : https://prove2.me/theorems/37440a05-f12d-4ba5-8793-a3b1c3386ca1
-- title:
--   Chapter ChapterSirkSingleTimeShift
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkSingleTimeShift`, source chapter `BookProof/ChapterSirkSingleTimeShift.lean`): Chapter ChapterSirkSingleTimeShift
--
--   Generated def bundle for ChapterSirkSingleTimeShift. See BookProof/ChapterSirkSingleTimeShift.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkSingleTimeShift.lean

import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterQgManifoldModeInstance
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib


/-!
# One shift, one finite time: the SIRK/Hashimoto algorithm needs no time discretization

The shift-invert rational Krylov (SIRK/Hashimoto) algorithm evaluates the propagator at a
**single finite time** `t`: it builds a rational approximant of `e^{−itA}` whose poles are
the *shifts*, and the only operator it ever applies is the **bounded** shift-invert
resolvent `(A − iℓ)⁻¹`.  There is therefore

* no time discretization (no step size, no number of steps, no Trotter splitting), and
* no boundedness requirement on the Hamiltonian: `‖(A − iℓ)⁻¹‖ ≤ 1/|ℓ|` holds for every
  self-adjoint `A`, however unbounded.

`BookProof.ChapterQgTimeStepping` analyses a time-stepping scheme (Crank–Nicolson) as *one
possible* way of producing the propagator.  This module records that time stepping is an
option, not a requirement, and supplies the statements the algorithm actually uses.

## What is proved

* `res_sub_res` — the first resolvent identity
  `(A − iℓ)⁻¹ − (A − im)⁻¹ = i(ℓ − m)(A − iℓ)⁻¹(A − im)⁻¹` for the project's
  `UnboundedSelfAdjoint` interface.
* `norm_res_neg` — `‖(A + iℓ)⁻¹y‖ = ‖(A − iℓ)⁻¹y‖`: the resolvent is normal, proved from
  the adjoint relation and the commutation of resolvents, with no spectral theorem.
* `StrongResAt T S ℓ` — strong convergence of the shift-invert operators at the **single**
  shift `ℓ`.
* `strongResAt_of_abs_sub_lt` — a Neumann/resolvent-identity step: convergence at `ℓ`
  gives convergence at every `m` with `|m − ℓ| < |ℓ|`.
* `strongResAt_neg`, `strongResAt_of_pos_of_pos`, **`strongResAt_of_ne_zero`** — hence
  convergence at *one* nonzero shift already gives convergence at *every* nonzero shift:
  the algorithm's choice of shift is immaterial.
* **`singleTime_flow_tendsto_of_strongResAt`** — and therefore, by Trotter–Kato, the
  approximants' propagators converge at **every single finite time** `t`, with no time
  discretization and no boundedness assumption anywhere.
* `isShiftInvertC_neg_resCLM_shift` — the Hashimoto shift-invert operator at the complex
  shift `γ = iℓ` is `−(A − iℓ)⁻¹` for every real `ℓ ≠ 0` (the case `ℓ = 1` is
  `BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM`).
* **`sirk_single_time_shiftInvert_bound`** — the end-to-end SIRK bound applied at one
  finite time: with `X = (A − iℓ)⁻¹` the bounded operator the algorithm iterates, the
  Krylov reduction approximates `e^{−itA}v` itself, at that single `t`; there is no time
  step anywhere in the statement.
* **`qgOuterFock_singleTime_shiftInvert_convergence`**,
  **`starobinsky_qgContinuum_singleTime_shiftInvert_convergence`** and
  **`starobinsky_qgManifold_singleTime_shiftInvert_convergence`** — the quantum-gravity
  instance: the mode-truncated Hamiltonians' shift-invert operators converge at *every*
  nonzero shift, and their propagators converge to the exact one at *every single finite
  time*.  This replaces the "choose a number of time steps per cutoff" formulation of
  `BookProof.ChapterQgTimeStepping.qgOuterFock_fullyDiscrete_convergence`.

Everything is `sorry`-free and `axiom`-free.
-/

open scoped InnerProductSpace

namespace BookProof.SirkSingleTime

open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. The resolvent identity and normality of the resolvent -/





/-! ## 2. Strong convergence at one shift gives strong convergence at every shift -/

/-- Strong convergence of the shift-invert operators at the single shift `ℓ`. -/
def StrongResAt (T : UnboundedSelfAdjoint E) (S : ℕ → UnboundedSelfAdjoint E) (l : ℝ) : Prop :=
  ∀ y : E, Tendsto (fun n => (S n).resCLM l y) atTop (𝓝 (T.resCLM l y))

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}













/-! ## 3. The Hashimoto shift-invert operator at an arbitrary complex shift `γ = iℓ` -/





/-! ## 4. The SIRK bound at a single finite time -/

open BookProof.ChapterSirkEndToEnd BookProof.ChapterH4 BookProof.ChapterH6

variable {Fin' : Type*} [NormedAddCommGroup Fin'] [InnerProductSpace ℂ Fin'] [CompleteSpace Fin']



/-! ## 5. The quantum-gravity instance: any single shift, any single finite time -/

open BookProof.QgTruncationResolvent BookProof.FarisLavine BookProof.EsaClosure
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL BookProof.QgOuterFockCoreFL

variable {ι : Type*}



open BookProof.QgContinuumModeInstance



open BookProof.QgManifoldModeInstance



end

end BookProof.SirkSingleTime


