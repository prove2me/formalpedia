-- Prove2me | Definitions.Def_ChapterParityQL
-- name    : ChapterParityQL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:46:36.557163+00:00
-- url     : https://prove2.me/theorems/ecb2e458-f598-4f06-a55c-e50b82d4b97d
-- title:
--   Chapter ParityQL
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterParityQL.lean`): generated def bundle for ChapterParityQL. See BookProof/ChapterParityQL.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityQL.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Mathlib


/-!
# Chapter "On the physical parity transformation and antiparticles" — the Standard-Model
quark-doublet parity is order four

This file continues the finite algebraic core of the `book.tex` chapter *"On the physical
parity transformation and antiparticles"* (`book.tex` line ~7522, §"Majorana spinors in
the Standard Model") begun in `ChapterParity`.

The chapter's generalized-parity (`ℤ₄`) transformation acts on the fields as

* Higgs doublet:  `φ(t,x⃗) ↦ i σ₂ φ(t,-x⃗)`  — internal part `i σ₂`, order four
  (`ChapterParity.higgsParity_order_four`);
* right-handed quarks:  `u_R, d_R ↦ i γ⁰ …(t,-x⃗)`  — internal part `i γ⁰ = mgamma 0`,
  order four (`ChapterParity.fermionParity_order_four`);
* left-handed quark doublet:  `Q_L(t,x⃗) ↦ -σ₂ γ⁰ Q_L(t,-x⃗)`.

The `Q_L` field carries **both** an `SU(2)_L` doublet index (on which `σ₂` acts) and a
Majorana spinor index (on which the parity `i γ⁰ = mgamma 0` acts), so the internal part of
its parity transformation is the Kronecker product `-(σ₂ ⊗ i γ⁰)` acting on
`ℂ² ⊗ ℂ⁴ ≅ ℂ⁸`.  This file proves that this operator is again **order exactly four**:

* `QLParity_sq`      : `(-σ₂ ⊗ iγ⁰)² = -1`  (using `σ₂² = 1` and `(iγ⁰)² = -1`);
* `QLParity_pow_four`: `(-σ₂ ⊗ iγ⁰)⁴ = 1`;
* `QLParity_order_four`: it is not an involution but `(…)⁴ = 1`.

Because the square is `-1` (and not `+1`), the parity of the right- and left-handed quarks
alike selects the double cover `Pin(3,1)` (rather than `Pin(1,3)`), the chapter's
conclusion.  The surrounding physical modelling (the full Standard-Model Lagrangian, the
`SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ ℤ₄` background symmetry) is left as prose.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped Kronecker

namespace BookProof.ChapterParityQL

open BookProof.ChapterA3
open BookProof.ChapterParity

/-- The internal (matrix) part of the generalized-parity transformation of the
left-handed quark doublet `Q_L ↦ -σ₂ γ⁰ Q_L(t,-x⃗)`.  The `SU(2)_L` factor `σ₂` acts on
the doublet index (`ℂ²`) and the Majorana parity `i γ⁰ = mgamma 0` acts on the spinor
index (`ℂ⁴`), so the whole operator is the Kronecker product `-(σ₂ ⊗ i γ⁰)` on
`ℂ² ⊗ ℂ⁴ ≅ ℂ⁸`. -/
noncomputable def QLParity : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  -(pauli2 ⊗ₖ mgamma 0)







end BookProof.ChapterParityQL


