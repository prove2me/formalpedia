-- Prove2me | Definitions.Def_ChapterGravityIrrep
-- name    : ChapterGravityIrrep
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:09:41.360494+00:00
-- url     : https://prove2.me/theorems/067a139e-7270-489a-b782-5d230c2627c5
-- title:
--   Chapter GravityIrrep
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityIrrep.lean`): generated def bundle for ChapterGravityIrrep. See BookProof/ChapterGravityIrrep.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityIrrep.lean

import Mathlib


/-!
# Chapter — Diffeomorphisms and gravity: the irreducible decomposition of a spatial tensor

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  In the Einstein–Cartan / teleparallel Hamiltonian
formalism the author decomposes the *spatial* torsion tensor `T_{ab}` (both free
indices projected by the spatial projector `χ` of Wave 69, so it lives on the
`3`-dimensional spatial hyperplane `v^⊥`) into three irreducible pieces relative
to the rotation group `SO(3)` of the spatial slice:

* the **antisymmetric part** `A_{ab} = T_{ab} − T_{ba}` (the book's `A_{ab}`);
* the **trace** `T = η^{ab} T_{ab}` (the book's scalar `T`);
* the **symmetric traceless part**
  `S_{ab} = T_{ab} + T_{ba} − (2/3) η_{ab} T` (the book's `S_{ab}`).

Since these tensors are fully spatial, and the induced spatial metric restricted
to `v^⊥` is positive definite (Wave 70), we model the spatial slice as the
Euclidean `3`-space `Fin 3` with `η_{ab} = δ_{ab}`.  The `2/3` factor is exactly
the one that makes `S` traceless *in three dimensions* (`tr δ = 3`), matching the
book.

This file makes the self-contained linear-algebra content precise.  A spatial
tensor is a `3 × 3` real matrix `M` (the book's `T_{ab}`), and we prove:

* `antisymPart_antisymm` — `A` is antisymmetric (`Aᵀ = −A`);
* `symTracelessPart_symm` — `S` is symmetric (`Sᵀ = S`);
* `trace_symTracelessPart` — `S` is traceless (`tr S = 0`);
* `irrep_reconstruction` — **headline**: the three pieces reassemble `M`,
  `M = ½ S + ½ A + ⅓ (tr M) · I`;
* `frob_symTraceless_antisym`, `frob_symTraceless_trace`, `frob_antisym_trace` —
  the three pieces are mutually orthogonal for the Frobenius inner product
  `⟨X, Y⟩ = ∑_{i,j} X_{ij} Y_{ij}`, i.e. the decomposition is orthogonal.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravityIrrep

open Matrix
open scoped BigOperators

/-- The **antisymmetric part** `A_{ab} = T_{ab} − T_{ba}` (the book's `A_{ab}`). -/
noncomputable def antisymPart (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  M - Mᵀ

/-- The **symmetric traceless part** `S_{ab} = T_{ab} + T_{ba} − (2/3) η_{ab} T`
(the book's `S_{ab}`), with `η_{ab} = δ_{ab}` on the Euclidean spatial slice. -/
noncomputable def symTracelessPart (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  M + Mᵀ - (2 / 3 * M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- The Frobenius inner product `⟨X, Y⟩ = ∑_{i,j} X_{ij} Y_{ij}` on spatial
tensors. -/
noncomputable def frobInner (X Y : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j















end BookProof.ChapterGravityIrrep


