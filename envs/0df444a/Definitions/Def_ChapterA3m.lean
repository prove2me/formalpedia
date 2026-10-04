-- Prove2me | Definitions.Def_ChapterA3m
-- name    : ChapterA3m
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:11:23.364577+00:00
-- url     : https://prove2.me/theorems/c6188d0b-9f67-4484-9aa4-265c60eb85a9
-- title:
--   Chapter A3m
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3m.lean`): generated def bundle for ChapterA3m. See BookProof/ChapterA3m.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3m.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3l
import Mathlib


/-!
# Chapter A, §A.3 — Note 51 / Lemma 52: the threefold braiding (`S₃`) structure

Source: `book.tex` §A.3, Notes 50–51 and Lemma 52 (line ~5560).

`ChapterA3l` introduced the **braiding (swap) operator** `τ` on the *two-fold*
tensor product `V ⊗ V` and the symmetric / antisymmetric decomposition it
induces (`projSym = ½(1+τ)`), showing that the symmetric tensor *square* is a
full-Lorentz subrepresentation — the Lemma-52 mechanism at the first symmetric
tensor power.

This file takes the **next step** toward the *arbitrary* `N`-fold symmetric
powers of Note 51: the **three-fold tensor product** `V ⊗ V ⊗ V`, carrier of the
symmetric cube `V ⊙ V ⊙ V` (which contains the top irrep `V⁺_{3/2}`), together
with the action of the symmetric group `S₃` by braidings.  On the
`4×4 ⊗ 4×4 ⊗ 4×4` Kronecker model (index type `((Fin 4 × Fin 4) × Fin 4)`,
left-associated) we build the two adjacent transposition operators
`τ₁₂, τ₂₃` and the long transposition `τ₁₃`, and prove:

* **Braiding relations** `swap12_kronecker`, `swap23_kronecker`,
  `swap13_kronecker`: each transposition conjugates a Kronecker product into the
  correspondingly permuted product.
* **`S₃` presentation**: involutivity `swap12_sq`, `swap23_sq`, `swap13_sq`
  (`τ² = 1`) and the **braid relation**
  `swap12*swap23*swap12 = swap13 = swap23*swap12*swap23` (`braid_left`,
  `braid_right`, `braid_rel`) — the Coxeter presentation of `S₃`.
* **Full-Lorentz invariance of the diagonal action**: the three transpositions
  each commute with the diagonal `Spin⁺` generator
  `A⊗1⊗1 + 1⊗A⊗1 + 1⊗1⊗A` (`swap12_spinGenDiag_comm`, …) and with the diagonal
  parity `γ⁰⊗γ⁰⊗γ⁰` (`swap12_parityDiag_comm`, …), because the totally
  symmetric diagonal action is invariant under any permutation of the slots.
* **Lemma 52 payoff for the symmetric cube**: the total symmetrizer
  `projSym3 = (1/6)·Σ_{g∈S₃} ρ(g)` is a **full-Lorentz** subrepresentation —
  `projSym3_spinGenDiag_comm` (diagonal `Spin⁺`-invariant) and
  `projSym3_parityDiag_comm` (parity-invariant) — so the *real* symmetric-cube
  construction is automatically a representation of the full Lorentz group,
  exactly as at the symmetric-square level in `ChapterA3l`.

Everything is a Kronecker-algebra consequence of `ChapterA3l`/`ChapterA3k` and is
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`),
with **no `EXTERNAL` hypothesis** (Note 50 / Weyl complete reducibility and the
extension to *all* `N`-fold symmetric powers remain the cited backbone).
-/

open Matrix
open scoped Kronecker

namespace BookProof.ChapterA3m

open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

/-- The `64`-dimensional carrier space `V ⊗ V ⊗ V` of three Dirac spinors,
modeled as `(4×4 ⊗ 4×4) ⊗ 4×4` matrices (left-associated Kronecker product,
index type `((Fin 4 × Fin 4) × Fin 4)`). -/
abbrev M3 := Matrix ((Fin 4 × Fin 4) × Fin 4) ((Fin 4 × Fin 4) × Fin 4) ℂ

/-! ## The three transposition (braiding) operators -/

/-- The transposition `τ₁₂` swapping the **first two** tensor slots,
`u ⊗ v ⊗ w ↦ v ⊗ u ⊗ w`.  Built as `τ ⊗ 1` from the two-fold braiding
`ChapterA3l.swap`. -/
noncomputable def swap12 : M3 := BookProof.ChapterA3l.swap ⊗ₖ 1

/-- The transposition `τ₂₃` swapping the **last two** tensor slots,
`u ⊗ v ⊗ w ↦ u ⊗ w ⊗ v`.  Entrywise the permutation matrix
`[b = (a₁, a₃, a₂)]`. -/
noncomputable def swap23 : M3 :=
  Matrix.of fun a b => if b.1.1 = a.1.1 ∧ b.1.2 = a.2 ∧ b.2 = a.1.2 then (1 : ℂ) else 0

/-- The long transposition `τ₁₃` swapping the **outer** slots,
`u ⊗ v ⊗ w ↦ w ⊗ v ⊗ u`.  Entrywise `[b = (a₃, a₂, a₁)]`. -/
noncomputable def swap13 : M3 :=
  Matrix.of fun a b => if b.1.1 = a.2 ∧ b.1.2 = a.1.2 ∧ b.2 = a.1.1 then (1 : ℂ) else 0

/-! ## Braiding relations -/

/-
Braiding relation for `τ₁₂`: `τ₁₂ · ((A⊗B)⊗C) = ((B⊗A)⊗C) · τ₁₂`.
-/


/-
Braiding relation for `τ₂₃`: `τ₂₃ · ((A⊗B)⊗C) = ((A⊗C)⊗B) · τ₂₃`.
-/


/-
Braiding relation for `τ₁₃`: `τ₁₃ · ((A⊗B)⊗C) = ((C⊗B)⊗A) · τ₁₃`.
-/


/-! ## The `S₃` presentation: involutivity and the braid relation -/

/-
`τ₁₂² = 1`.
-/


/-
`τ₂₃² = 1`.
-/


/-
`τ₁₃² = 1`.
-/


/-
Braid relation, left form: `τ₁₂ τ₂₃ τ₁₂ = τ₁₃`.
-/


/-
Braid relation, right form: `τ₂₃ τ₁₂ τ₂₃ = τ₁₃`.
-/




/-! ## The diagonal Lorentz / parity action on `V ⊗ V ⊗ V` -/

/-- The **diagonal** `Spin⁺(3,1)` generator on `V ⊗ V ⊗ V`:
`γ^μγ^ν ⊗ 1 ⊗ 1 + 1 ⊗ γ^μγ^ν ⊗ 1 + 1 ⊗ 1 ⊗ γ^μγ^ν`. -/
noncomputable def spinGenDiag3 (μ ν : Fin 4) : M3 :=
  (spinGen μ ν ⊗ₖ 1) ⊗ₖ 1 + (1 ⊗ₖ spinGen μ ν) ⊗ₖ 1 + (1 ⊗ₖ 1) ⊗ₖ spinGen μ ν

/-- The **diagonal** parity operator on `V ⊗ V ⊗ V`: `γ⁰ ⊗ γ⁰ ⊗ γ⁰`. -/
noncomputable def parityDiag3 : M3 := (mgamma 0 ⊗ₖ mgamma 0) ⊗ₖ mgamma 0

/-! ## Each transposition commutes with the diagonal action -/













/-! ## The total symmetrizer and its full-Lorentz invariance -/

/-- The total symmetrizer `projSym3 = (1/6)·Σ_{g∈S₃} ρ(g)` onto the symmetric
cube `V ⊙ V ⊙ V`.  The six group elements are realized as
`1, τ₁₂, τ₂₃, τ₁₂τ₂₃, τ₂₃τ₁₂, τ₁₃`. -/
noncomputable def projSym3 : M3 :=
  (6 : ℂ)⁻¹ • (1 + swap12 + swap23 + swap12 * swap23 + swap23 * swap12 + swap13)

/-
**Lemma 52 payoff (symmetric-cube step).** The symmetric cube is a diagonal
`Spin⁺` subrepresentation: `projSym3` commutes with every diagonal Lorentz
generator.
-/


/-
**Lemma 52 payoff (symmetric-cube step).** The symmetric cube is also
parity-invariant: `projSym3` commutes with diagonal parity `γ⁰⊗γ⁰⊗γ⁰`.  Thus the
real symmetric-cube construction is automatically a representation of the full
Lorentz group.
-/


/-
`projSym3` is idempotent — a genuine projector onto the symmetric cube.
This encodes the group identity `(Σ_{g∈S₃} g)² = 6·Σ_{g∈S₃} g`: the six braiding
operators `1, τ₁₂, τ₂₃, τ₁₂τ₂₃, τ₂₃τ₁₂, τ₁₃` are exactly the image of `S₃` under
the permutation representation, closed under multiplication.
-/


end BookProof.ChapterA3m


