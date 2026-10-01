-- Prove2me | Definitions.Def_ChapterNavierStokesEulerian
-- name    : ChapterNavierStokesEulerian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:16:47.769266+00:00
-- url     : https://prove2.me/theorems/ba6e5c5c-d18a-4d8f-93d3-03d6b383b14b
-- title:
--   Chapter NavierStokesEulerian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesEulerian.lean`): generated def bundle for ChapterNavierStokesEulerian. See BookProof/ChapterNavierStokesEulerian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEulerian.lean

import Definitions.Def_ChapterNavierStokesFlow
import Mathlib


/-!
# The **Eulerian** constraints of the derivatives-as-fields construction

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier–Stokes equations"* (~4133–4216), together with the
constraint taxonomy of the chapter *"Gauge transformations, constrained systems
and conditioned probability"* (~2222–2323).

`BookProof.ChapterNavierStokesFlow` formalizes the field-with-derivatives
construction (`fieldTaylor`, `field_evaluates_to_value`), the canonical
commutation relations of the derivative modes, the Lagrangian (parcel) side of
the change of variables (`lagrangian_velocity`, `volume_preservation_constraint`)
and the complete flow of the finite truncation.  This module supplies the
**Eulerian** counterpart: the constraints that make `u_{k,j}` and `u_{k,jk}`
legitimate Eulerian canonical variables rather than arbitrary tensors.

Following the book's own taxonomy the constraints split in two kinds:

* **gauge-generator constraints** — the field-to-derivative relations
  `u_{i,j} = ∂_j u_i` (`derivativeField_relates_to_field`),
  `u_{i,jk} = ∂_k u_{i,j}` (`derivativeField_second`) and their Clairaut
  consequence `u_{i,jk} = u_{i,kj}` (`derivativeField_consistency`): they have no
  explicit solution, so they are imposed by declaring a gauge generator
  (`book.tex` ~2286);
* **explicit-solution constraints** — incompressibility `∂_j u_j = 0`
  (`eulerian_divergence_constraint`), which needs no gauge generator because the
  substitution `u_{3,3} = −(u_{1,1} + u_{2,2})` solves it outright
  (`book.tex` ~4194–4197); the BRST charge is then only the elegant packaging of
  that constraint, not a first-class gauge generator.

The partial derivatives are taken in the *directional* form
`dirDeriv f j x = d/dt f(x + t e_j)|_{t=0}`, which is the exact meaning of
"the derivative of the field along the `j`-th coordinate" used by the book, and
which `dirDeriv_eq` identifies with the Fréchet derivative in the direction `e_j`
whenever the field is differentiable.

Nothing here claims anything about the *continuum* Navier–Stokes problem: these
are the algebraic/differential identities that the finite truncation of
`ChapterNavierStokesFlow` is the shadow of.  Everything is `sorry`-free and
`axiom`-free.
-/

namespace BookProof.NavierStokesEulerian

open BookProof.NavierStokesFlow Matrix

/-! ## Directional (partial) derivatives of a Eulerian field -/

/-- The `j`-th coordinate direction of `ℝ³`. -/
def evec (j : Fin 3) : Fin 3 → ℝ := Pi.single j 1

/-- The partial derivative `∂_j f` of a field on `ℝ³`, in directional form. -/
noncomputable def dirDeriv (f : (Fin 3 → ℝ) → ℝ) (j : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  deriv (fun t : ℝ => f (x + t • evec j)) 0







/-! ## A.5 — the Eulerian constraints -/















/-- The cyclic shear field `u_i(x) = x_{i+1}`. -/
def cyclicShear (y : Fin 3 → ℝ) (i : Fin 3) : ℝ := y (i + 1)



/-! ## E.3 — the BRST charge is not Hermitian -/





end BookProof.NavierStokesEulerian


