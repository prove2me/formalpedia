-- Prove2me | Definitions.Def_ChapterStoneEigenflow
-- name    : ChapterStoneEigenflow
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:28:50.065876+00:00
-- url     : https://prove2.me/theorems/335e279e-c055-461f-8d9e-216de2e5a321
-- title:
--   Chapter StoneEigenflow
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterStoneEigenflow.lean`): generated def bundle for ChapterStoneEigenflow. See BookProof/ChapterStoneEigenflow.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneEigenflow.lean

import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Mathlib

/-!
# Explicit dynamics on eigenvectors: the Stone flow acts by a phase

`BookProof.ChapterStoneBridge` produces, from essential self-adjointness of a symmetric
operator `Hc` on a dense core `D`, a self-adjoint extension `T` and a complete unitary
flow `U` solving the Schrödinger equation `d/dt (U t x) = −i T (U t x)`
(`BookProof.StoneBridge.exists_stone_flow_of_esa`).  That statement is an *existence*
statement: it says nothing about what the flow does to a concrete vector.

For all the Hamiltonians of the quadratic family in this development the core carries an
orthonormal *total family of eigenvectors* — the (translated, modulated, rotated) product
Hermite functions — and on such a vector the dynamics must be explicit.  This module proves
that it is:

* `isSelfAdjointExtension_eigenvector` — a self-adjoint extension of `Hc` still has `ψ` as
  an eigenvector, with the same eigenvalue;
* `stoneFlow_apply_eigenvector` — **the headline**: if `T ψ = λψ` with `λ` real and `U` is
  *any* Stone flow for `T`, then `U t ψ = e^{−iλt} ψ` for every `t`;
* `stoneFlow_apply_core_eigenvector` — the two combined, stated for an eigenvector of the
  core operator;
* `exists_diagonal_stone_flow` — for a densely defined symmetric essentially self-adjoint
  operator with *any* family of eigenvectors in the core, a flow exists which acts on each
  of them by the corresponding phase.

The proof of the headline does not use the spectral theorem.  Writing
`φ(t) = ⟪ψ, U t ψ⟫`, the Schrödinger equation and symmetry of `T` give the scalar ODE
`φ' = −iλφ`, so `φ(t) = e^{−iλt}‖ψ‖²`; since `U t` is isometric this is the equality case
of the Cauchy–Schwarz inequality, i.e. `‖U t ψ − e^{−iλt}ψ‖ = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
namespace BookProof.StoneEigenflow

end BookProof.StoneEigenflow


