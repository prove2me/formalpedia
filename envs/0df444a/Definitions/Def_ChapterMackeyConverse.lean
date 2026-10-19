-- Prove2me | Definitions.Def_ChapterMackeyConverse
-- name    : ChapterMackeyConverse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:39:03.238378+00:00
-- url     : https://prove2.me/theorems/83d8b172-7a49-437a-ab8b-bea7cf0774b9
-- title:
--   Chapter MackeyConverse
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMackeyConverse.lean`): generated def bundle for ChapterMackeyConverse. See BookProof/ChapterMackeyConverse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyConverse.lean

import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterMackeyCocycle
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterPvmMeasure
import Mathlib


/-!
# The converse of Mackey's imprimitivity theorem over a continuous base

`BookProof.ChapterMackeyQuasiInvariant` proves the **induced direction** over a
measure-theoretic base: a quasi-invariant measure and a measurable unitary cocycle give a
system of imprimitivity on `L²(X, μ; K)`.  The converse — every system of imprimitivity
over such a base is unitarily equivalent to an induced one — was formalized only for a
**discrete** base (`BookProof.ChapterMackeyGeneralBase`).  This file proves the converse
over a continuous base, for a system with a **cyclic** vector (the multiplicity-one case,
to which the general case reduces by decomposing into cyclic subspaces).

## Statement

A *continuous-base system of imprimitivity* is a unitary representation `U` of `G` on `H`
together with a projection-valued measure `P` on the measurable `G`-space `X` obeying
Mackey's covariance relation `U(g) P(E) = P(g·E) U(g)`.  If `ψ` is a cyclic vector for `P`
and `μ = ‖P(·)ψ‖²` is the measure it defines, then

* `μ` is **quasi-invariant** (`QuasiInvariant μ G`) — this is forced, not assumed;
* there is a unitary `W : L²(X, μ) ≃ H` carrying the projection-valued measure to
  multiplication by indicators, and
* a measurable cocycle `u : G → X → ℂ` of **modulus one** with
  `W⁻¹ U(g) W f (x) = u g x · √(dens μ g x) · f(g⁻¹ x)` a.e.,

i.e. the system is unitarily equivalent to the induced system of
`BookProof.ChapterMackeyQuasiInvariant` built from `μ` and `u`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterMackeyConverse

open BookProof.ChapterPvmMeasure BookProof.ChapterMackeyQuasiInvariant
open BookProof.ChapterPvmCyclicUnitary BookProof.ChapterMackeyCocycle

variable {G X H : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **system of imprimitivity over a continuous base**: a unitary representation of `G`
on `H`, a projection-valued measure on the measurable `G`-space `X`, and Mackey's
covariance relation. -/
structure ContinuousImprimitivitySystem (G X H : Type*) [Group G] [MeasurableSpace X]
    [MulAction G X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The unitary representation. -/
  U : G →* (H ≃ₗᵢ[ℂ] H)
  /-- The projection-valued measure over the base. -/
  P : Pvm X H
  /-- The action is measurable. -/
  measurable : ∀ g : G, Measurable fun x : X => g • x
  /-- Mackey's covariance relation `U(g) P(E) = P(g·E) U(g)`. -/
  covariant : ∀ (g : G) {E : Set X}, MeasurableSet E → ∀ v : H,
    U g (P.p E v) = P.p ((fun x => g • x) '' E) (U g v)



end BookProof.ChapterMackeyConverse


