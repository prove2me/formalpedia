-- Prove2me | Definitions.Def_ChapterFarisLavineOnly
-- name    : ChapterFarisLavineOnly
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T15:53:36.495357+00:00
-- url     : https://prove2.me/theorems/2aaf42b6-fd44-4342-8ef8-ebedb8bda159
-- title:
--   The Lean 4 theorem `abs_le_sum_abs` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFarisLavineOnly.lean`): generated def bundle for ChapterFarisLavineOnly. See BookProof/ChapterFarisLavineOnly.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineOnly.lean

import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockFullFL
import Mathlib


/-!
# Essential self-adjointness **only through Faris–Lavine**

The development contains three independent routes to essential self-adjointness of the
field-space Hamiltonians: the Carleman flux criterion
(`BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint`, used by
`BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn`), the weighted Schur/Kato–Rellich
gates, and the commutator criterion of Faris–Lavine
(`BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine`).

Only the last one **lifts** from the one-particle Hilbert space to the outer Fock space.
The reason is structural and is made explicit here:

* a Faris–Lavine certificate consists of a comparison operator `N` — always the Friedrichs
  extension of a positive one-particle operator — and a commutator bound `±i[H,N] ≤ cN`;
* the Friedrichs extension lifts to the `ℓ²`-direct sum (`dsComparison`: symmetry,
  positivity and surjectivity of `N + 1` are fibrewise, and the fibre solutions of
  `(N+1)x = f` are automatically square-summable), and
* the commutator form of the lift is the **sum** of the fibre commutator forms
  (`dsFibOp_hasSum_commForm`), so the bound lifts with the *same* constant `c`.

Neither of the other two routes has this property: a Carleman flux estimate and a Schur
weight are statements about a *fixed* one-particle basis and its shells, and nothing in them
survives the passage to `⊕ₙ L²(ℝ^{d·n})` — the number of shells of the `n`-particle sector
grows with `n`, and the constants degrade.

This module therefore replaces the Carleman route by the Faris–Lavine route at the place it
enters the main line: the essential self-adjointness of a kinetic-plus-squares Hamiltonian
**on the Gauss–polynomial core itself**.

## What is proved

* `BookProof.QgOuterFockCoreFL.CoreData.esa_on_core` — the missing abstract step:
  Faris–Lavine gives essential self-adjointness not merely of the extension `ext` on the
  whole domain of the comparison operator, but of the original operator **on the graph core**
  (the relative bound transports the graph approximation of `N` to a graph approximation of
  `H`, which is exactly the hypothesis of
  `BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core`).
* `sqSumOp_esa_farisLavine` — **the Faris–Lavine replacement for
  `BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn`**: for an arbitrary real signature
  `κ` and an arbitrary finite family of linear forms, `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` is
  essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᴰ)`, proved from the two
  Faris–Lavine inequalities of `BookProof.ChapterSqSumFarisLavine` against the Friedrichs
  oscillator `N₁ = −Δ + ‖x‖²/4`, with no Carleman flux estimate anywhere.  The Schur data
  are supplied by the trivial bounds, so the statement carries no hypotheses.
* `SqFamily.secHam_esa_fl`, `SqFamily.outerHam_esa_fl` — the same for every sector of a
  uniform family, and hence for the Hamiltonian on the finite-particle core of the outer
  Fock space: **the finite-particle-core statement, too, is now Faris–Lavine only.**
* `SqFamily.esa_farisLavine` — the certificate itself, collected in one statement: the
  comparison operator is the lifted Friedrichs extension, the relative bound and the
  commutator bound hold with constants `flK`, `flc` independent of the particle number, and
  the conclusion is essential self-adjointness on the lifted domain together with the
  extension property on the finite-particle core.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FarisLavineOnly

open Finset
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL BookProof.SqSumOuterFamily

/-! ## 1. Every sector of a uniform family, by Faris–Lavine -/





/-! ## 2. A single kinetic-plus-squares Hamiltonian, by Faris–Lavine -/

section Single

variable {D : ℕ} {R : Type} [Fintype R]

/-- The trivial signature bound: `|κ_I| ≤ Σ_J |κ_J|`. -/
theorem abs_le_sum_abs (kappa : Fin D → ℝ) (I : Fin D) :
    |kappa I| ≤ ∑ J : Fin D, |kappa J| :=
  Finset.single_le_sum (f := fun J => |kappa J|) (fun _ _ => abs_nonneg _) (Finset.mem_univ I)

/-- The total `ℓ¹` mass of the coefficient matrix of the linear forms. -/
def totalMass (v : R → Fin D → ℝ) : ℝ := ∑ r : R, ∑ I : Fin D, |v r I|

theorem totalMass_nonneg (v : R → Fin D → ℝ) : 0 ≤ totalMass v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem row_le_totalMass (v : R → Fin D → ℝ) (r : R) :
    ∑ I : Fin D, |v r I| ≤ totalMass v :=
  Finset.single_le_sum (f := fun s => ∑ I : Fin D, |v s I|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ r)

theorem col_le_totalMass (v : R → Fin D → ℝ) (I : Fin D) :
    ∑ r : R, |v r I| ≤ totalMass v := by
  refine Finset.sum_le_sum fun r _ => ?_
  exact Finset.single_le_sum (f := fun J => |v r J|) (fun _ _ => abs_nonneg _) (Finset.mem_univ I)

/-- The constant family whose every sector carries the same kinetic-plus-squares
Hamiltonian: the vehicle that lets the uniform-family machinery be used for a single
operator. -/
def constFamily (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) : SqFamily where
  dim := fun _ => D
  R := fun _ => R
  finR := fun _ => inferInstance
  kap := fun _ => kappa
  vv := fun _ => v
  km := ∑ J : Fin D, |kappa J|
  a := totalMass v
  b := totalMass v
  km_nonneg := Finset.sum_nonneg fun _ _ => abs_nonneg _
  a_nonneg := totalMass_nonneg v
  b_nonneg := totalMass_nonneg v
  kap_le := fun _ I => abs_le_sum_abs kappa I
  row_le := fun _ r => row_le_totalMass v r
  col_le := fun _ I => col_le_totalMass v I

@[simp] theorem constFamily_secHam (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (n : ℕ) :
    (constFamily kappa v).secHam n = sqSumOp kappa v := rfl



end Single

end BookProof.FarisLavineOnly


